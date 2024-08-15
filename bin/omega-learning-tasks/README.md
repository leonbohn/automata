# `omega-learning-tasks`
Tools to generate tasks for passive learning of omega automata.
## Usage
At the moment there are two functionalities for this repo:
### Generate new Tasks with target Automaton
`cargo run -- gen`

Some parameters can be adjusted in the `main` function. Of particular interest are the following:
- `automata_sizes: Vec<usize>`: list of sizes of target automata to be generated
- `automata_per_size`: number of different automata per automaton size
- `train_sizes: Vec<usize>`: list of training set sizes to be generated
- `num_sets`: number of different sets per training set size

Tasks with DBAs and DPAs as target automata are generated. All tasks are saved in the directory `/data`.
### Run Sprout Learning Algorithm on all Tasks with Target Automaton
`cargo run -- sprout`

The results of the learning procedure are saved in the directory of the corresponding task. Statistics can be found in the `result.csv` file.

Tasks are only run when `result.csv` does not exist yet.


### Generate new Tasks with randomly labeled Samples
`cargo run -- genrand`

Some parameters can be adjusted in the `main` function. Of particular interest are the following:
- `word_lens: Vec<usize>`: list of lengths of words
- `sparsieties: Vec<f64>`: list of sparsities (should be densities)
- `num_sets`: number of different sets per pair of word length and density

All tasks are saved in the directory `/data/rand_sets`.

### Run Sprout Learning Algorithm on all Tasks with randomly labeled Samples
`cargo run -- sproutrand`

The algorithm is run for both Büchi and parity acceptance. The results are saved in the directory of the corresponding task. Statistics can be found in the `result.csv` file.

Tasks are only run when `result.csv` does not exist yet.


