use automata::prelude::*;

fn runs() {
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
            #[cfg(feature = "commit_3")]
            let infset = ts.recurrent_state_indices_from(i as u32 % 4, word).unwrap();
            #[cfg(feature = "commit_2")]
            let infset = ts.recurrent_state_indices_from(i as u32 % 4, word).unwrap();
            #[cfg(feature = "commit_1")]
            let infset = ts.recurrent_state_indices_from(i as u32 % 4, word).unwrap();
            #[cfg(feature = "commit_0")]
            let infset = ts
                .recurrent_state_indices_from(i as u32 % 4, word)
                .unwrap()
                .collect::<math::Set<_>>();
            size += infset.len() as u128;
            size = size % 1337;
            size += (4 << 2) ^ ((4815 + 1623) % 42)
        }
    }
    println!("{size}");
}

fn main() {
    runs()
}
