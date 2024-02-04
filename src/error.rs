use anchor_lang::prelude::*;

#[error]
pub enum EscrowError {
    #[msg("Invalid trade configuration")]
    InvalidTrade,
    #[msg("State does not match input accounts")]
    InvalidState,
    #[msg("Missing mint")]
    MissingMint,
    #[msg("Invalid mint for trade")]
    InvalidMint,
}