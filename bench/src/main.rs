use automata::prelude::*;

fn main() {
    let ts = DTS::builder()
        .default_color(Void)
        .with_transitions([
            (0, 'a', 1),
            (0, 'b', 0),
            (1, 'a', 2),
            (1, 'b', 1),
            (2, 'a', 3),
            (2, 'b', 1),
            (3, 'a', 1),
            (3, 'b', 0),
        ])
        .into_dts_with_initial(0);

    let words = vec![
        upw!("abba"),
        upw!("babbabba", "bababbabbabbba"),
        upw!("aa"),
        upw!("babbabba", "babbaaaaaaaaaaaa"),
        upw!("bbababaaaaba"),
        upw!("babbabba", "babbbababaabbabbba"),
        upw!("abba"),
        upw!("aba"),
        upw!("abaaabababababababbababbababba"),
        upw!("babbabba", "bababbabbabbbababbabaa"),
    ];
    let mut size: u128 = 0;
    for i in 0..10000 {
        for word in &words {
            let infset = ts
                .recurrent_state_indices_from(i as u32 % 4, word)
                .expect("alsdf");
            // .collect::<math::Set<_>>();
            size += infset.len() as u128;
        }
    }
    println!("total size after 1000 executions: {size}");
}
