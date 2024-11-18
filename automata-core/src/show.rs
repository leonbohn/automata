use itertools::Itertools;

use crate::Void;

/// This method should display the time in a sensible format. If it is less than a second, it should
/// only display the milliseconds and microseconds. If it is less than a minute, it should display
/// the seconds and milliseconds. If it is less than an hour, it should display the minutes and
/// seconds. If it is less than a day, it should display the hours and minutes. If it is more than a
/// day, it should display the days and hours.
pub fn show_duration(duration: std::time::Duration) -> String {
    let ms = duration.as_millis();
    let us = duration.as_micros();
    let s = duration.as_secs();
    let m = s / 60;
    let h = m / 60;
    let d = h / 24;

    if d > 0 {
        format!("{}d {}h", d, h % 24)
    } else if h > 0 {
        format!("{}h {}m", h, m % 60)
    } else if m > 0 {
        format!("{}m {}s", m, s % 60)
    } else if s > 0 {
        format!("{}s {}ms", s, ms % 1000)
    } else if ms > 0 {
        format!("{}ms {}us", ms, us % 1000)
    } else {
        format!("{}us", us)
    }
}

impl<C: Show> Show for (C, Void) {
    fn show(&self) -> String {
        self.0.show()
    }
}

impl<C: Show> Show for (Void, C) {
    fn show(&self) -> String {
        self.1.show()
    }
}

impl Show for u8 {
    fn show(&self) -> String {
        self.to_string()
    }
}

impl Show for (Void, Void) {
    fn show(&self) -> String {
        "-".to_string()
    }
}
impl<C: Show> Show for (C, &Void) {
    fn show(&self) -> String {
        self.0.show()
    }
}

impl<C: Show> Show for (&Void, C) {
    fn show(&self) -> String {
        self.1.show()
    }
}

impl Show for (&Void, &Void) {
    fn show(&self) -> String {
        "-".to_string()
    }
}

/// Helper trait which can be used to display states, transitions and such.
pub trait Show {
    /// Returns a human readable representation of `self`, for a state index that should be
    /// for example q0, q1, q2, ... and for a transition (q0, a, q1) it should be (q0, a, q1).
    /// Just use something that makes sense. This is mainly used for debugging purposes.
    fn show(&self) -> String;
    /// Show a collection of the thing, for a collection of states this should be {q0, q1, q2, ...}
    /// and for a collection of transitions it should be {(q0, a, q1), (q1, b, q2), ...}.
    /// By default this is unimplemented.
    fn show_collection<'a, I>(_iter: I) -> String
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        unimplemented!("This operation makes no sense.")
    }
}

impl Show for Option<usize> {
    fn show(&self) -> String {
        match self {
            None => "".to_string(),
            Some(x) => x.show(),
        }
    }

    fn show_collection<'a, I>(iter: I) -> String
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        usize::show_collection(iter.into_iter().filter_map(|x| x.as_ref()))
    }
}

impl Show for char {
    fn show(&self) -> String {
        self.to_string()
    }

    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
    {
        format!(
            "\"{}\"",
            iter.into_iter().map(|sym| sym.to_string()).join("")
        )
    }
}
impl Show for u32 {
    fn show(&self) -> String {
        self.to_string()
    }
    fn show_collection<'a, I>(iter: I) -> String
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        format!(
            "[{}]",
            itertools::Itertools::join(&mut iter.into_iter().map(|x| x.show()), ", ")
        )
    }
}

impl Show for usize {
    fn show(&self) -> String {
        self.to_string()
    }
    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        format!(
            "[{}]",
            itertools::Itertools::join(&mut iter.into_iter().map(|x| x.show()), ", ")
        )
    }
}
impl Show for String {
    fn show(&self) -> String {
        self.clone()
    }
}

impl Show for () {
    fn show(&self) -> String {
        "-".into()
    }
    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(_iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        "-".to_string()
    }
}

impl<S: Show> Show for [S] {
    fn show(&self) -> String {
        format!(
            "\"{}\"",
            itertools::Itertools::join(&mut self.iter().map(|x| x.show()), "")
        )
    }

    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        format!(
            "{{{}}}",
            itertools::Itertools::join(&mut iter.into_iter().map(|x| x.show()), ", ")
        )
    }
}

impl<S: Show> Show for Vec<S> {
    fn show(&self) -> String {
        S::show_collection(self.iter())
    }
}

impl<S: Show, T: Show> Show for (S, T) {
    fn show(&self) -> String {
        format!("({}, {})", self.0.show(), self.1.show())
    }
}

impl Show for bool {
    fn show(&self) -> String {
        match self {
            true => "+",
            false => "-",
        }
        .to_string()
    }

    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        format!("{{{}}}", iter.into_iter().map(Show::show).join(", "))
    }
}

impl<S: Show> Show for &S {
    fn show(&self) -> String {
        S::show(*self)
    }
}
