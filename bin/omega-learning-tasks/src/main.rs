use csv::Writer;
use itertools::{Either, Itertools};
use rand::random;
use rayon::prelude::*;
use std::{collections::HashMap, env, fs, path::PathBuf, time::Duration};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, Layer};

use automata::{
    automaton::InfiniteWordAutomaton,
    hoa::output::WriteHoa,
    prelude::*,
    random::{generate_random_dba, generate_random_dpa, generate_random_omega_words},
};
use automata_learning::passive::{
    sprout::{sprout, SproutError},
    OmegaSample,
};
use math::set::IndexSet;
use tracing::{debug, info, warn};

fn main() {
    // initialize logger
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .pretty()
                .with_writer(std::io::stderr)
                .with_filter(tracing_subscriber::filter::LevelFilter::INFO),
        )
        .init();

    let args: Vec<String> = env::args().collect();
    if args.contains(&"gen".to_string()) {
        // (re)generate tasks
        println!("Start generating learning tasks");
        let automata_sizes = vec![4, 8, 16];
        let automata_per_size = 10;
        let train_sizes = vec![100, 1000, 10000];
        let test_size = 10000;
        let num_sets = 10;
        let lambda = 0.95;
        generate_tasks(
            automata_sizes,
            automata_per_size,
            train_sizes,
            test_size,
            num_sets,
            lambda,
        );
    }
    if args.contains(&"sprout".to_string()) {
        println!("Running sprout learner on all tasks");
        run_sprout();
    }
    if args.contains(&"genrand".to_string()) {
        println!("Generating randomly labeled samples");
        let word_lens = vec![2, 3, 4, 5, 6, 7, 8];
        let sparsities = vec![0.01, 0.02, 0.05, 0.1, 0.2];
        let num_sets = 100;
        generate_randomly_labeled(word_lens, sparsities, num_sets);
    }
    if args.contains(&"sproutrand".to_string()) {
        println!("Running sprout learner on randomly labeled samples");
        run_sprout_rand();
    }
    println!("Done");
}

pub fn run_sprout() {
    // load task directories
    let mut task_dirs = vec![];
    let entries = fs::read_dir("data/tasks").expect("No learning tasks available");
    for entry in entries.flatten() {
        if let Ok(file_type) = entry.file_type() {
            if file_type.is_dir() {
                task_dirs.push(entry.path());
            }
        } else {
            println!("Couldn't get file type for {:?}", entry.path());
        }
    }
    task_dirs
        .clone()
        .into_par_iter()
        .map(load_sample)
        .enumerate()
        .for_each(|(i, sample)| {
            let dir = &task_dirs[i];
            info!("task {i} \"{:?}\"", dir.to_string_lossy());
            // check if task was already computed
            if dir.join("result_minesc.csv").exists() {
                info!("Already computed. Skip.");
                return;
            }
            debug!("starting learner for task {i}");
            let time = std::time::Instant::now();
            if dir.to_string_lossy().contains("dba") {
                let result = sprout(sample, BuchiCondition);
                let elapsed = time.elapsed();
                match result {
                    Ok(learned) => {
                        info!(
                            "task {i} \"{:?}\" learning took {} ms",
                            dir.to_string_lossy(),
                            elapsed.as_millis()
                        );
                        export_automaton(
                            format!("{}/learned_minesc.hoa", dir.to_str().unwrap()),
                            &learned,
                        );
                        export_sprout_result(dir, &learned, elapsed);
                    }
                    Err(SproutError::Timeout(ts)) => {
                        warn!(
                            "exceeded timeout on task {i} \"{:?}\" at size {:?}",
                            dir.to_string_lossy(),
                            ts.size(),
                        );
                        let mut wtr = Writer::from_path(dir.join("result_minesc.csv"))
                            .expect("creating file failed");
                        wtr.write_record(["timeout_size", &format!("{}", ts.size())])
                            .unwrap();
                        wtr.flush().unwrap();
                    }
                    Err(SproutError::Threshold(thresh, learned, ts)) => {
                        warn!(
                            "exceeded threshold {:?} on task {i} \"{:?}\" at size {:?}",
                            thresh,
                            dir.to_string_lossy(),
                            ts.size(),
                        );
                        export_automaton(
                            format!("{}/learned_min_esc.hoa", dir.to_str().unwrap()),
                            &learned,
                        );
                        export_sprout_result(dir, &learned, elapsed);
                    }
                }
            } else {
                let result = sprout(sample, MinEvenParityCondition);
                let elapsed = time.elapsed();
                match result {
                    Ok(learned) => {
                        info!(
                            "task {i} \"{:?}\" learning took {} ms",
                            dir.to_string_lossy(),
                            elapsed.as_millis()
                        );
                        export_automaton(
                            format!("{}/learned_minesc.hoa", dir.to_str().unwrap()),
                            &learned,
                        );
                        export_sprout_result(dir, &learned, elapsed);
                    }
                    Err(SproutError::Timeout(ts)) => {
                        warn!(
                            "exceeded timeout on task {i} \"{:?}\" at size {:?}",
                            dir.to_string_lossy(),
                            ts.size(),
                        );
                        let mut wtr = Writer::from_path(dir.join("result_minesc.csv"))
                            .expect("creating file failed");
                        wtr.write_record(["timeout_size", &format!("{}", ts.size())])
                            .unwrap();
                        wtr.flush().unwrap();
                    }
                    Err(SproutError::Threshold(thresh, learned, ts)) => {
                        warn!(
                            "exceeded threshold {:?} on task {i} \"{:?}\" at size {:?}",
                            thresh,
                            dir.to_string_lossy(),
                            ts.size(),
                        );
                        export_automaton(
                            format!("{}/learned_minesc.hoa", dir.to_str().unwrap()),
                            &learned,
                        );
                        export_sprout_result(dir, &learned, elapsed);
                    }
                }
            }
        });
}

pub fn generate_randomly_labeled(word_lens: Vec<usize>, sparsities: Vec<f64>, num_sets: usize) {
    for len in word_lens {
        let max_words = (2_u32.pow(len as u32 + 1) - 1) * (2_u32.pow(len as u32 + 1) - 2);
        for sparsity in sparsities.iter() {
            let size = (max_words as f64 * sparsity).round() as usize;
            for set_index in 0..num_sets {
                let (set, _) = generate_set(2, len, len, size, 0);
                let labeled: Vec<_> = set.into_iter().map(|w| (w, random::<bool>())).collect();

                let filename = rand_set_name(len, (sparsity * 100.0).round() as usize, set_index);
                export_labelled_set(filename, &labeled);
            }
        }
    }
}

pub fn run_sprout_rand() {
    // load task directories
    let mut task_dirs = vec![];
    let entries = fs::read_dir("data/rand_sets").expect("No learning tasks available");
    for entry in entries.flatten() {
        if let Ok(file_type) = entry.file_type() {
            if file_type.is_dir() {
                task_dirs.push(entry.path());
            }
        } else {
            println!("Couldn't get file type for {:?}", entry.path());
        }
    }
    task_dirs
        .clone()
        .into_par_iter()
        .map(load_sample)
        .enumerate()
        .for_each(|(i, sample)| {
            let dir = &task_dirs[i];
            info!("task {i} \"{:?}\"", dir.to_string_lossy());
            // check if task was already computed
            if dir.join("result.csv").exists() {
                info!("Already computed. Skip.");
                return;
            }
            // learn DBA
            debug!("starting dba learner for task {i}");
            let time = std::time::Instant::now();
            let result = sprout(sample.clone(), BuchiCondition);
            let elapsed = time.elapsed();
            let size;
            let status;
            match result {
                Ok(learned) => {
                    info!(
                        "task {i} \"{:?}\" learning took {} ms",
                        dir.to_string_lossy(),
                        elapsed.as_millis()
                    );
                    export_automaton(
                        format!("{}/learned_dba.hoa", dir.to_str().unwrap()),
                        &learned,
                    );
                    size = learned.size();
                    status = "success";
                }
                Err(SproutError::Timeout(ts)) => {
                    warn!(
                        "exceeded timeout on task {i} \"{:?}\" at size {:?}",
                        dir.to_string_lossy(),
                        ts.size(),
                    );
                    size = ts.size();
                    status = "timeout"
                }
                Err(SproutError::Threshold(thresh, learned, ts)) => {
                    warn!(
                        "exceeded threshold {:?} on task {i} \"{:?}\" at size {:?}",
                        thresh,
                        dir.to_string_lossy(),
                        ts.size(),
                    );
                    export_automaton(
                        format!("{}/learned_dba.hoa", dir.to_str().unwrap()),
                        &learned,
                    );
                    size = ts.size();
                    status = "threshold";
                }
            }
            let mut wtr = Writer::from_path(dir.join("result.csv"))
                        .expect("creating file failed");
            wtr.write_record(["dba_status", &format!("{}", status)]).unwrap();
            wtr.write_record(["dba_size", &format!("{}", size)]).unwrap();            
            wtr.write_record(["dba_time_ms", &format!("{}", elapsed.as_millis())]).unwrap();
            
            // DPA
            debug!("starting dpa learner for task {i}");
            let time = std::time::Instant::now();
            let result = sprout(sample, MinEvenParityCondition);
            let elapsed = time.elapsed();
            let size;
            let status;
            match result {
                Ok(learned) => {
                    info!(
                        "task {i} \"{:?}\" learning took {} ms",
                        dir.to_string_lossy(),
                        elapsed.as_millis()
                    );
                    export_automaton(
                        format!("{}/learned_dpa.hoa", dir.to_str().unwrap()),
                        &learned,
                    );
                    size = learned.size();
                    status = "success";
                }
                Err(SproutError::Timeout(ts)) => {
                    warn!(
                        "exceeded timeout on task {i} \"{:?}\" at size {:?}",
                        dir.to_string_lossy(),
                        ts.size(),
                    );
                    size = ts.size();
                    status = "timeout"
                }
                Err(SproutError::Threshold(thresh, learned, ts)) => {
                    warn!(
                        "exceeded threshold {:?} on task {i} \"{:?}\" at size {:?}",
                        thresh,
                        dir.to_string_lossy(),
                        ts.size(),
                    );
                    export_automaton(
                        format!("{}/learned_dpa.hoa", dir.to_str().unwrap()),
                        &learned,
                    );
                    size = ts.size();
                    status = "threshold";
                }
            }
            wtr.write_record(["dpa_status", &format!("{}", status)]).unwrap();
            wtr.write_record(["dpa_size", &format!("{}", size)]).unwrap();            
            wtr.write_record(["dpa_time_ms", &format!("{}", elapsed.as_millis())]).unwrap();
            wtr.flush().unwrap();
        });
}

/// Generate a sample of ultimately periodic words by loading the training set from
/// the learning task located in the given dircetory.
pub fn load_sample(dir: PathBuf) -> OmegaSample {
    let mut rdr = csv::Reader::from_path(dir.join("train.csv")).expect("No training set found");
    let (pos_words, neg_words): (Vec<_>, Vec<_>) = rdr.deserialize().partition_map(|result| {
        let (spoke, cycle, class): (String, String, bool) =
            result.expect("Failed to read training set");
        let word = upw!(spoke, cycle);
        if class {
            Either::Left(word)
        } else {
            Either::Right(word)
        }
    });

    // todo: check for size of alphabet
    let alphabet = CharAlphabet::of_size(2);
    OmegaSample::new_omega_from_pos_neg(alphabet, pos_words, neg_words)
}

/// generate set of learning tasks for DBA and DPA.
pub fn generate_tasks(
    automata_sizes: Vec<usize>,
    automata_per_size: usize,
    train_sizes: Vec<usize>,
    test_size: usize,
    num_sets: usize,
    lambda: f64,
) {
    // set parameters
    let num_symbols = 2;
    let num_prios = 5;
    fs::create_dir_all("data/automata").unwrap();
    fs::create_dir_all("data/sets").unwrap();

    // generate DBAs
    println!("generating DBAs");
    let mut dbas = HashMap::new();
    for &size in automata_sizes.iter() {
        let mut auts = vec![];
        for i in 0..automata_per_size {
            let dba = generate_dba(num_symbols, size, lambda);
            export_automaton(aut_name(size, i, "dba".to_string()), &dba);
            auts.push(dba);
        }
        dbas.insert(size, auts);
    }

    // generate DPAs
    println!("generating DPAs");
    let mut dpas = HashMap::new();
    for &size in automata_sizes.iter() {
        let mut auts = vec![];
        for i in 0..automata_per_size {
            let dpa = generate_dpa(num_symbols, size, num_prios, lambda);
            export_automaton(aut_name(size, i, "dpa".to_string()), &dpa);
            auts.push(dpa);
        }
        dpas.insert(size, auts);
    }

    // generate train and test sets
    println!("generating word sets");
    let mut sets_dba = HashMap::new();
    let mut sets_dpa = HashMap::new();
    for &aut_size in automata_sizes.iter() {
        for &train_size in train_sizes.iter() {
            let mut sets_of_size_dba = vec![];
            let mut sets_of_size_dpa = vec![];
            for i in 0..num_sets {
                // DBA sets
                let len_spoke = std::cmp::max(8, aut_size);
                let len_cycle = std::cmp::max(8, aut_size);
                let (train, test) =
                    generate_set(num_symbols, len_spoke, len_cycle, train_size, test_size);
                export_set(set_name(aut_size, train_size, i, true, "dba"), &train);
                export_set(set_name(aut_size, train_size, i, false, "dba"), &test);
                sets_of_size_dba.push((train, test));
                // DPA sets
                let len_spoke = aut_size;
                let len_cycle = 2 * aut_size + (aut_size - 1).pow(2);
                let (train, test) =
                    generate_set(num_symbols, len_spoke, len_cycle, train_size, test_size);
                export_set(set_name(aut_size, train_size, i, true, "dpa"), &train);
                export_set(set_name(aut_size, train_size, i, false, "dpa"), &test);
                sets_of_size_dpa.push((train, test));
            }
            sets_dba.insert((aut_size, train_size), sets_of_size_dba);
            sets_dpa.insert((aut_size, train_size), sets_of_size_dpa);
        }
    }

    // label dba sets
    println!("labelling dba sets");
    for &aut_size in automata_sizes.iter() {
        for (aut_index, dba) in dbas[&aut_size].iter().enumerate() {
            for &train_size in train_sizes.iter() {
                for (set_index, (tr, te)) in sets_dba[&(aut_size, train_size)].iter().enumerate() {
                    let train = label_set(dba, tr);
                    let test = label_set(dba, te);
                    // export as learning task
                    export_task(
                        task_name(
                            aut_size,
                            train_size,
                            aut_index,
                            set_index,
                            "dba".to_string(),
                        ),
                        dba,
                        &train,
                        &test,
                    );
                }
            }
        }
    }

    // label dpa sets
    println!("labelling dpa sets");
    for &aut_size in automata_sizes.iter() {
        for (aut_index, dpa) in dpas[&aut_size].iter().enumerate() {
            for &train_size in train_sizes.iter() {
                for (set_index, (tr, te)) in sets_dpa[&(aut_size, train_size)].iter().enumerate() {
                    let train = label_set(dpa, tr);
                    let test = label_set(dpa, te);
                    // export as learning task
                    export_task(
                        task_name(
                            aut_size,
                            train_size,
                            aut_index,
                            set_index,
                            "dpa".to_string(),
                        ),
                        dpa,
                        &train,
                        &test,
                    );
                }
            }
        }
    }
}

/// Generate a random DBA with `aut_size` states on an alphabet of size `num_symbols`.
/// The parameter `lambda` is used to draw the acceptance condition from a continuous Bernoulli distribution.
/// The produced automaton has an informative right congruence.
pub fn generate_dba(num_symbols: usize, aut_size: usize, lambda: f64) -> DBA {
    let gen_size = aut_size + (aut_size as f32).log2().round() as usize - 1;
    let mut dba: DBA;
    loop {
        dba = generate_random_dba(num_symbols, gen_size, lambda).streamlined();
        // check if dba has the correct size
        if dba.size() == aut_size {
            let equiv_dpa = dba
                .clone()
                .map_edge_colors(|c| if c { 0 } else { 1 })
                .collect_dpa();
            // check if automaton has informative right congruence
            if equiv_dpa.is_informative_right_congruent() {
                break;
            }
        }
    }
    dba
}

/// Generate a random DPA with `aut_size` states on an alphabet of size `num_symbols`.
/// The parameter `lambda` is used to draw the acceptance condition from a continuous Bernoulli distribution.
/// The produced automaton has an informative right congruence.
pub fn generate_dpa(num_symbols: usize, aut_size: usize, num_prios: u8, lambda: f64) -> DPA {
    let gen_size = aut_size + (aut_size as f32).log2().round() as usize - 1;
    let mut dpa: DPA;
    loop {
        dpa = generate_random_dpa(num_symbols, gen_size, num_prios, lambda)
            .streamlined()
            .collect_dpa();
        // check if dpa has the correct size and has informative right congruence
        if dpa.size() == aut_size && dpa.is_informative_right_congruent() {
            break;
        }
    }
    dpa
}

/// Generate a training set, test set pair of random ultimately periodic words.
/// The length of spoke and cycle are drawn uniformly and the used alphabet is of size `num_symbols`.
pub fn generate_set(
    num_symbols: usize,
    len_spoke: usize,
    len_cycle: usize,
    train_size: usize,
    test_size: usize,
) -> (
    IndexSet<ReducedOmegaWord<char>>,
    IndexSet<ReducedOmegaWord<char>>,
) {
    let alphabet = CharAlphabet::of_size(num_symbols);
    let mut training_set = generate_random_omega_words(
        &alphabet,
        0,
        len_spoke,
        1,
        len_cycle,
        train_size + test_size,
    );
    let test_set = training_set.split_off(train_size);
    (training_set, test_set)
}

/// Label a `set` of [`ReducedOmegaWord`]s with the result of the given automaton.
pub fn label_set<Z, C>(
    aut: &InfiniteWordAutomaton<CharAlphabet, Z, Void, C, true>,
    set: &IndexSet<ReducedOmegaWord<char>>,
) -> Vec<(ReducedOmegaWord<char>, bool)>
where
    Z: OmegaSemantics<Void, C, Output = bool>,
    C: Color,
{
    set.into_iter()
        .map(|w| (w.clone(), aut.accepts(w)))
        .collect()
}

/// Write the given automaton to the given `path` in HOA format
pub fn export_automaton<AUT: WriteHoa>(file: String, aut: &AUT) {
    fs::write(file, aut.to_hoa()).expect("Unable to write file");
}

/// Give filename for an omega automaton
pub fn aut_name(aut_size: usize, aut_index: usize, acc_type: String) -> String {
    format!("data/automata/{acc_type}__aut_size={aut_size}__{aut_index:0>2}.hoa")
}

/// Write the given set to the given `path` as csv
pub fn export_set(file: String, set: &IndexSet<ReducedOmegaWord<char>>) {
    let mut wtr = Writer::from_path(file).expect("creating file failed");
    for w in set.iter() {
        wtr.write_record(&[
            w.spoke().iter().collect::<String>(),
            w.cycle().iter().collect(),
        ])
        .unwrap();
    }
    wtr.flush().unwrap();
}

/// Load labelled set from csv. Split into positively and negatively labelled words
pub fn load_set(
    path: &std::path::Path,
    file: String,
) -> (Vec<ReducedOmegaWord<char>>, Vec<ReducedOmegaWord<char>>) {
    let mut rdr = csv::Reader::from_path(path.join(file)).expect("No training set found");
    rdr.deserialize().partition_map(|result| {
        let (spoke, cycle, class): (String, String, bool) =
            result.expect("Failed to read training set");
        let word = upw!(spoke, cycle);
        if class {
            Either::Left(word)
        } else {
            Either::Right(word)
        }
    })
}

/// Give filename for a set of omega words
pub fn set_name(
    aut_size: usize,
    set_size: usize,
    set_index: usize,
    train: bool,
    acc_type: &str,
) -> String {
    let class = if train { "train" } else { "test" };
    format!("data/sets/word_set__{acc_type}__aut_size={aut_size}__sample_size={set_size}__{set_index:0>2}_{class}.csv")
}

/// Give filename for a set of radnomly labeled omega words
pub fn rand_set_name(word_len: usize, sparsity: usize, set_index: usize) -> String {
    let name = format!("word_set__word_len={word_len}__sparsity={sparsity}__set_index{set_index:0>2}");
    fs::create_dir_all(format!("data/rand_sets/{name}")).unwrap();
    format!("data/rand_sets/{name}/train.csv")
}

pub fn export_labelled_set(file: String, set: &[(ReducedOmegaWord<char>, bool)]) {
    let mut wtr = Writer::from_path(file).expect("creating file failed");
    wtr.write_record(["spoke", "cycle", "acceptance"]).unwrap();
    for (w, r) in set.iter() {
        wtr.write_record([
            w.spoke().iter().collect(),
            w.cycle().iter().collect(),
            format!("{r:?}"),
        ])
        .unwrap();
    }
    wtr.flush().unwrap();
}

/// Write the given omega automata learning task to the given `path` in HOA format
pub fn export_task<AUT: WriteHoa>(
    name: String,
    aut: &AUT,
    train: &[(ReducedOmegaWord<char>, bool)],
    test: &[(ReducedOmegaWord<char>, bool)],
) {
    // remove old results if they exist
    let _ = fs::remove_dir_all(format!("data/tasks/{name}"));
    // export new data
    fs::create_dir_all(format!("data/tasks/{name}")).unwrap();
    export_automaton(format!("data/tasks/{name}/aut.hoa"), aut);
    export_labelled_set(format!("data/tasks/{name}/train.csv"), train);
    export_labelled_set(format!("data/tasks/{name}/test.csv"), test);
    export_settings(
        format!("data/tasks/{name}/settings.txt"),
        name,
        aut.alphabet().size(),
        aut.size(),
        train.len(),
        test.len(),
    );
}

pub fn task_name(
    aut_size: usize,
    set_size: usize,
    aut_index: usize,
    set_index: usize,
    acc_type: String,
) -> String {
    format!("{acc_type}_task__aut_size={aut_size:0>2}__sample_size={set_size:0>5}__{acc_type}{aut_index:0>2}__sample{set_index:0>2}")
}

pub fn export_settings(
    file: String,
    name: String,
    num_symbols: usize,
    aut_size: usize,
    train_size: usize,
    test_size: usize,
) {
    let acc_type = if name.contains("dba") { "dba" } else { "dpa" };
    let mut wtr = Writer::from_path(file).expect("creating file failed");
    wtr.write_record(["name", &name]).unwrap();
    wtr.write_record(["aut_type", acc_type]).unwrap();
    wtr.write_record(["num_symbols", &format!("{num_symbols}")])
        .unwrap();
    wtr.write_record(["aut_size", &format!("{aut_size}")])
        .unwrap();
    wtr.write_record(["train_size", &format!("{train_size}")])
        .unwrap();
    wtr.write_record(["test_size", &format!("{test_size}")])
        .unwrap();
    wtr.flush().unwrap();
}

/// Score test set and export results
pub fn export_sprout_result<Z, C>(
    task_dir: &std::path::Path,
    learned: &InfiniteWordAutomaton<CharAlphabet, Z, Void, C, true>,
    elapsed: Duration,
) where
    Z: OmegaSemantics<Void, C, Output = bool>,
    C: Color,
{
    // load test set
    let (test_pos, test_neg) = load_set(task_dir, "test.csv".to_string());
    let pos_count = test_pos.len();
    let neg_count = test_neg.len();
    let test_size = pos_count + neg_count;
    // score test set
    let mut scored_pos = label_set(learned, &test_pos.into_iter().collect());
    let scored_neg = label_set(learned, &test_neg.into_iter().collect());
    let pos_correct = scored_pos.iter().filter(|(_, b)| *b).count();
    let neg_correct = scored_neg.iter().filter(|(_, b)| !b).count();
    let total_correct = pos_correct + neg_correct;

    let path_str = task_dir.to_str().unwrap();
    scored_pos.extend(scored_neg);
    export_labelled_set(format!("{}/test_learned_minesc.csv", path_str), &scored_pos);

    // export %correct, %pos/neg correct, aut size in result file
    let mut wtr =
        Writer::from_path(task_dir.join("result_minesc.csv")).expect("creating file failed");
    wtr.write_record(["learned_aut_size", &format!("{}", learned.size())])
        .unwrap();
    wtr.write_record(["scored_correct", &format!("{total_correct}")])
        .unwrap();
    wtr.write_record([
        "scored_correct%",
        &format!("{}", total_correct as f64 / test_size as f64),
    ])
    .unwrap();
    wtr.write_record(["pos_correct", &format!("{pos_correct}")])
        .unwrap();
    wtr.write_record([
        "pos_correct%",
        &format!("{}", pos_correct as f64 / pos_count as f64),
    ])
    .unwrap();
    wtr.write_record(["neg_correct", &format!("{neg_correct}")])
        .unwrap();
    wtr.write_record([
        "neg_correct%",
        &format!("{}", neg_correct as f64 / neg_count as f64),
    ])
    .unwrap();
    wtr.write_record(["pos_count", &format!("{pos_count}")])
        .unwrap();
    wtr.write_record([
        "pos_count%",
        &format!("{}", pos_count as f64 / test_size as f64),
    ])
    .unwrap();
    wtr.write_record(["neg_count", &format!("{neg_count}")])
        .unwrap();
    wtr.write_record([
        "neg_count%",
        &format!("{}", neg_count as f64 / test_size as f64),
    ])
    .unwrap();
    wtr.write_record(["time_ms", &format!("{}", elapsed.as_millis())])
        .unwrap();
    wtr.flush().unwrap();
}
