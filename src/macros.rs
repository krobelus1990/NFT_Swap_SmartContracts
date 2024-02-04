#[macro_export]
macro_rules! gen_seeds {
    ($seed:expr, $bump:expr) => {
        &[
            &[
                $seed.key().as_ref(),
                &[$bump],
            ][..]
        ]
    };
}
