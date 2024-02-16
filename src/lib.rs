//! Cofre: a general purpose escrow program.
//!
//! Based on Anchor's example Escrow program, which is in turn inspired by PaulX tutorial seen here
//! https://paulx.dev/blog/2021/01/14/programming-on-solana-an-introduction/
//!
//! User (maker) constructs an escrow deal:
//! - SPL X|SOL they will offer and amount
//! - SPL Y|SOL they want in return and amount
//! - Program will transfer the specified offer amount into an escrowed account, with authority|signer
//!   being a PDA generated with a static seed
//!
//! Once this escrow is initialised, either:
//! 1. User (Taker) can call the exchange function to exchange their Y for X
//! - This will close the escrow token account, and escrow account and no longer be usable
//! OR
//! 2. If no one has exchanged, the maker can close the escrow account
//! - maker will get back their escrowed token X funds

#[macro_use]
mod macros;
mod error;

use {
    vipers::{assert_owner, assert_keys_eq},
    error::EscrowError,
    anchor_lang::prelude::*,
    anchor_lang::solana_program,
    anchor_spl::token::{self, Token, Mint, TokenAccount, Transfer,  InitializeAccount},
    spl_token::solana_program::native_token::sol_to_lamports
};

declare_id!("Cofre5DxTYsWtWKrby3hLVg8pM5RePf96sCa7HJMwDeZ");

#[program]
pub mod ninja {
    use super::*;

    type TokenResult<'info> = Result<Account<'info, TokenAccount>, ProgramError>;
    type MintResult<'info> = Result<Account<'info, Mint>, ProgramError>;

    pub fn initialize<'info>(
        ctx: Context<'_, '_, '_, 'info, Initialize<'info>>,
        maker_amount: u64,
        taker_amount: u64,
        vault_bump: u8,
    ) -> ProgramResult {
        let main_accounts: (TokenResult, TokenResult) =
            (Account::try_from(&ctx.accounts.from_maker_account),
             Account::try_from(&ctx.accounts.to_maker_account));

        let mint_accounts: (Option<MintResult>, Option<MintResult>) =
            (ctx.remaining_accounts.get(0).map(Account::try_from),
             ctx.remaining_accounts.get(1).map(Account::try_from));

        let trade = match main_accounts {
            (Ok(from_token), Ok(to_token)) =>
                match mint_accounts {
                    (Some(Ok(from_mint)), Some(Ok(to_mint))) => {
                        assert_keys_eq!(
                            to_token.owner, ctx.accounts.maker.key(),
                            "to_token.owner != maker"
                        );
                        assert_keys_eq!(
                            from_token.mint, from_mint.key(),
                            "from_token does not match its corresponding mint"
                        );
                        assert_keys_eq!(
                            to_token.mint, to_mint.key(),
                            "to_token does not match its corresponding mint"
                        );
                        assert_keys_eq!(
                            to_token.mint, to_mint.key(),
                            "to_token does not match its corresponding mint"
                        );
                        if from_mint.key() == to_mint.key() {
                            msg!("InvalidTrade: Same from and to mints");
                            return Err(EscrowError::InvalidTrade.into());
                        }

                        ctx.accounts.initialize_token_vault(from_mint.to_account_info(), vault_bump)?;
                        ctx.accounts.transfer_tokens_to_vault(maker_amount)?;

                        Trade::SplSpl {
                            // TODO Remove from_token
                            from_token: from_token.key(),
                            from_mint: from_mint.key(),
                            to_token: to_token.key(),
                            to_mint: to_mint.key(),
                        }
                    }
                    (None, _) | (_, None) => {
                        msg!("MissingMint: Missing mint for SplSpl trade");
                        return Err(EscrowError::MissingMint.into());
                    }
                    _ => {
                        msg!("InvalidMint: Invalid mint account for SplSpl trade");
                        return Err(EscrowError::InvalidMint.into());
                    }
                },
            (Ok(from_token), Err(_)) =>
                match mint_accounts {
                    (Some(Ok(from_mint)), None) => {
                        assert_keys_eq!(
                            from_token.mint, from_mint,
                            "from_token does not match its corresponding mint"
                        );

                        ctx.accounts.initialize_token_vault(from_mint.to_account_info(), vault_bump)?;
                        ctx.accounts.transfer_tokens_to_vault(maker_amount)?;

                        Trade::SplSol {
                            from_token: from_token.key(),
                            from_mint: from_mint.key(),
                            to_native: ctx.accounts.to_maker_account.key(),
                        }
                    }
                    (None, _) => {
                        msg!("MissingMint: Missing mint for SplSol trade");
                        return Err(EscrowError::MissingMint.into());
                    }
                    _ => {
                        // TODO If maker does not have an ATA CREATED YET it lands here
                        msg!("InvalidMint: Invalid mint account for SplSol trade");
                        return Err(EscrowError::InvalidTrade.into());
                    }
                }
            (Err(_), Ok(to_token)) =>
                match mint_accounts {
                    (Some(Ok(to_mint)), None) => {
                        assert_keys_eq!(
                            to_token.mint, to_mint,
                            "to_token does not match its corresponding mint"
                        );
                        assert_keys_eq!(
                            ctx.accounts.maker, ctx.accounts.from_maker_account,
                            "maker must be the same as from_maker_account"
                        );

                        // SOL Transfer to vault
                        ctx.accounts.initialize_native_vault(maker_amount)?;
                        assert_owner!(ctx.accounts.escrow_vault, solana_program::system_program::ID);

                        Trade::SolSpl {
                            // TODO Remove from_native
                            from_native: ctx.accounts.maker.key(),
                            to_token: to_token.key(),
                            to_mint: to_mint.key(),
                        }
                    }
                    (None, _) => {
                        msg!("MissingMint: Missing mint for SolSpl trade");
                        return Err(EscrowError::MissingMint.into());
                    }
                    _ => {
                        msg!("InvalidMint: Invalid mint account for SolSpl trade");
                        return Err(EscrowError::InvalidTrade.into());
                    }
                }
            (Err(_), Err(_)) => {
                msg!("InvalidTrade: Invalid from and to accounts. Must be SplSpl, SplSol, or SolSpl");
                return Err(EscrowError::InvalidTrade.into());
            }
        };

        let escrow_state = &mut ctx.accounts.escrow_state;
        escrow_state.maker = ctx.accounts.maker.key();
        escrow_state.trade = trade;
        escrow_state.vault = ctx.accounts.escrow_vault.key();
        escrow_state.maker_amount = maker_amount;
        escrow_state.taker_amount = taker_amount;

        Ok(())
    }

    pub fn cancel(ctx: Context<Cancel>, vault_bump: u8) -> ProgramResult {
        match ctx.accounts.escrow_state.trade {
            Trade::SplSpl { from_token, .. } | Trade::SplSol { from_token, .. } => {
                assert_keys_eq!(
                    ctx.accounts.from_maker_account, from_token,
                    "escrow_state.trade.from_token does not match from_maker_account"
                );
                assert_owner!(ctx.accounts.escrow_vault, token::ID);

                // Transfer SPL from Vault to Maker
                ctx.accounts.transfer_to_maker_token(vault_bump)?;

                // Close SPL Vault
                ctx.accounts.close_escrow_vault_token(vault_bump)?;
            }
            Trade::SolSpl { from_native, .. } => {
                assert_keys_eq!(
                    ctx.accounts.from_maker_account, from_native,
                    "escrow_state.trade.from_native does not match from_maker_account"
                );
                assert_owner!(ctx.accounts.escrow_vault, solana_program::system_program::ID);

                // Transfer all SOL in Escrow Vault back to maker, will close it as well
                ctx.accounts.close_escrow_vault_native(vault_bump)?;
            }
        }

        Ok(())
    }

    pub fn exchange(ctx: Context<Exchange>, vault_bump: u8) -> ProgramResult {
        match ctx.accounts.escrow_state.trade {
            Trade::SplSpl { to_token, .. } => {
                assert_keys_eq!(
                    to_token, ctx.accounts.to_maker_account,
                    "to_token in escrow_state is different than provided to_maker_account"
                );
                assert_keys_eq!(
                    ctx.accounts.escrow_state.maker, ctx.accounts.maker,
                    "maker in escrow_state is different than provided maker"
                );

                // Transfer Vault SPL -> Taker SPL
                ctx.accounts.transfer_to_taker_token(vault_bump)?;

                // Transfer Taker SPL -> Maker SPL
                ctx.accounts.transfer_to_maker_token(vault_bump)?;

                // Close Escrow Vault
                ctx.accounts.close_escrow_vault_token(vault_bump)?;
            }
            Trade::SolSpl { from_native, to_token, .. } => {
                assert_keys_eq!(
                    to_token, ctx.accounts.to_maker_account,
                    "to_token in escrow_state is different than provided to_maker_account"
                );
                assert_keys_eq!(
                    ctx.accounts.taker, ctx.accounts.to_taker_account,
                    "taker is different than provided to_taker_account"
                );
                assert_keys_eq!(
                    from_native, ctx.accounts.maker,
                    "from_token in state is different than provided maker"
                );
                assert_owner!(ctx.accounts.escrow_vault, solana_program::system_program::ID);

                // Transfer Vault SOL -> Taker SOL
                ctx.accounts.transfer_to_taker_native(vault_bump)?;

                // Transfer Taker SPL -> Maker SPL
                ctx.accounts.transfer_to_maker_token(vault_bump)?;

                // Close Escrow Vault
                ctx.accounts.close_escrow_vault_native(vault_bump)?;
            }
            Trade::SplSol { to_native, .. } => {
                assert_keys_eq!(
                    to_native, ctx.accounts.to_maker_account,
                    "to_native in escrow_state is different than provided to_maker_account"
                );
                assert_keys_eq!(
                    ctx.accounts.maker, ctx.accounts.to_maker_account,
                    "maker is different than provided to_maker_account"
                );

                // TODO Conditionally initialize ATA for toTakerAccount
                // Transfer Vault SPL -> Taker SPL
                ctx.accounts.transfer_to_taker_token(vault_bump)?;

                // Transfer Taker SOL -> Maker SOL
                ctx.accounts.transfer_to_maker_native()?;

                // Close Escrow Vault
                ctx.accounts.close_escrow_vault_token(vault_bump)?;
            }
        }

        Ok(())
    }
}

#[derive(Accounts)]
#[instruction(maker_amount: u64, taker_amount: u64, vault_bump: u8)]
pub struct Initialize<'info> {
    #[account(mut)]
    pub maker: Signer<'info>,
    #[account(mut)]
    pub from_maker_account: AccountInfo<'info>,
    pub to_maker_account: AccountInfo<'info>,
    #[account(
        mut,
        seeds = [escrow_state.key().as_ref()],
        bump = vault_bump
    )]
    pub escrow_vault: AccountInfo<'info>,
    #[account(init, payer = maker, space = 8 + EscrowState::LEN)]
    pub escrow_state: Account<'info, EscrowState>,
    pub system_program: Program<'info, System>,
    pub token_program: Program<'info, Token>,
    pub rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
#[instruction(vault_bump: u8)]
pub struct Exchange<'info> {
    pub taker: Signer<'info>,
    #[account(mut)]
    pub from_taker_account: AccountInfo<'info>,
    #[account(mut)]
    pub to_taker_account: AccountInfo<'info>,
    #[account(mut)]
    pub maker: AccountInfo<'info>,
    #[account(mut)]
    pub to_maker_account: AccountInfo<'info>,
    // TODO Fix close = maker for PDA
    #[account(
        mut,
        seeds = [escrow_state.key().as_ref()],
        bump = vault_bump
    )]
    pub escrow_vault: AccountInfo<'info>,
    #[account(
        mut,
        constraint = escrow_state.vault == escrow_vault.key(),
        constraint = escrow_state.maker == maker.key(),
        close = maker
    )]
    pub escrow_state: Account<'info, EscrowState>,
    pub token_program: Program<'info, Token>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
#[instruction(vault_bump: u8)]
pub struct Cancel<'info> {
    #[account(mut)]
    pub maker: Signer<'info>,

    // This could be an SPL or SOL account
    #[account(mut)]
    pub from_maker_account: AccountInfo<'info>,

    // Vault used to hold native SOL or SPL tokens
    // TODO Fix close = maker for PDA
    #[account(
        mut,
        seeds = [escrow_state.key().as_ref()],
        bump = vault_bump
    )]
    pub escrow_vault: AccountInfo<'info>,

    #[account(
        mut,
        constraint = escrow_state.maker == maker.key(),
        constraint = escrow_state.vault == escrow_vault.key(),
        close = maker
    )]
    pub escrow_state: Account<'info, EscrowState>,

    pub token_program: Program<'info, Token>,

    pub system_program: Program<'info, System>,
}

#[account]
pub struct EscrowState {
    pub maker: Pubkey,
    pub vault: Pubkey,
    pub trade: Trade,
    // TODO Change these to f64 to support decimals
    pub maker_amount: u64,
    pub taker_amount: u64,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub enum Trade {
    SplSpl {
        from_token: Pubkey,
        from_mint: Pubkey,
        to_token: Pubkey,
        to_mint: Pubkey,
    },
    SolSpl {
        from_native: Pubkey,
        to_token: Pubkey,
        to_mint: Pubkey,
    },
    SplSol {
        from_token: Pubkey,
        from_mint: Pubkey,
        to_native: Pubkey,
    },
}

// TODO Derive this automagically
impl EscrowState {
    pub const LEN: usize =
        32 +       // Maker Pubkey
        32 +       // Vault Pubkey
        1 +        // Trade Enum Discriminator
        (32 * 4) + // Trade Max Pubkeys
        8 +        // Maker amount
        8;         // Taker amount
}

impl<'info> Initialize<'info> {
    fn initialize_token_vault(&self, mint: AccountInfo<'info>, vault_bump: u8) -> ProgramResult {
        let space = anchor_spl::token::TokenAccount::LEN;
        let lamports = self.rent.minimum_balance(space);
        anchor_lang::solana_program::program::invoke_signed(
            &solana_program::system_instruction::create_account(
                self.maker.key,
                self.escrow_vault.key,
                lamports,
                space as u64,
                &token::ID,
            ),
            &[
                self.maker.to_account_info(),
                self.escrow_vault.to_account_info(),
                self.system_program.to_account_info(),
            ],
            gen_seeds!(self.escrow_state, vault_bump),
        )?;

        let cpi_accounts = InitializeAccount {
            account: self.escrow_vault.to_account_info(),
            mint,
            authority: self.escrow_vault.to_account_info(),
            rent: self.rent.to_account_info(),
        };

        let cpi_program = self.token_program.to_account_info();
        let cpi_ctx = CpiContext::new(cpi_program, cpi_accounts);

        token::initialize_account(cpi_ctx)
    }

    fn initialize_native_vault(&self, amount: u64) -> ProgramResult {
        // TODO Make sure the amount of lamports is more than required space for rent 0 bytes
        // let lamports = self.rent.minimum_balance(0);
        solana_program::program::invoke(
            &solana_program::system_instruction::transfer(
                self.maker.key,
                self.escrow_vault.key,
                sol_to_lamports(amount as f64),
            ),
            &[
                self.maker.to_account_info(),
                self.escrow_vault.to_account_info(),
                self.system_program.to_account_info()
            ],
        )
    }

    fn transfer_tokens_to_vault(&self, amount: u64) -> ProgramResult {
        let cpi_accounts = Transfer {
            from: self.from_maker_account.to_account_info(),
            to: self.escrow_vault.to_account_info(),
            authority: self.maker.to_account_info(),
        };
        let cpi_program = self.token_program.to_account_info();
        let cpi_ctx = CpiContext::new(cpi_program, cpi_accounts);

        token::transfer(
            cpi_ctx,
            amount,
        )
    }
}

impl<'info> Cancel<'info> {
    fn transfer_to_maker_token(&self, vault_bump: u8) -> ProgramResult {
        let cpi_accounts = Transfer {
            from: self.escrow_vault.to_account_info(),
            to: self.from_maker_account.to_account_info(),
            authority: self.escrow_vault.to_account_info(),
        };
        let cpi_program = self.token_program.to_account_info();
        let cpi_ctx = CpiContext::new(cpi_program, cpi_accounts);

        token::transfer(
            cpi_ctx.with_signer(gen_seeds!(self.escrow_state, vault_bump)),
            self.escrow_state.maker_amount,
        )
    }

    fn close_escrow_vault_token(&self, vault_bump: u8) -> ProgramResult {
        let cpi_accounts = anchor_spl::token::CloseAccount {
            account: self.escrow_vault.to_account_info(),
            destination: self.maker.to_account_info(),
            authority: self.escrow_vault.to_account_info(),
        };
        let cpi_program = self.token_program.to_account_info();
        let cpi_ctx = CpiContext::new(cpi_program, cpi_accounts);

        token::close_account(cpi_ctx.with_signer(gen_seeds!(self.escrow_state, vault_bump)))

    }

    fn close_escrow_vault_native(&self, vault_bump: u8) -> ProgramResult {
        solana_program::program::invoke_signed(
            &solana_program::system_instruction::transfer(
                self.escrow_vault.key,
                self.maker.key,
                self.escrow_vault.lamports(),
            ),
            &[
                self.escrow_vault.to_account_info(),
                self.maker.to_account_info(),
                self.system_program.to_account_info()
            ],
            gen_seeds!(self.escrow_state, vault_bump),
        )
    }
}

impl<'info> Exchange<'info> {
    fn transfer_to_taker_token(&self, vault_bump: u8) -> ProgramResult {
        let cpi_accounts = Transfer {
            from: self.escrow_vault.to_account_info(),
            to: self.to_taker_account.to_account_info(),
            authority: self.escrow_vault.to_account_info(),
        };
        let cpi_program = self.token_program.to_account_info();
        let cpi_ctx = CpiContext::new(cpi_program, cpi_accounts);

        token::transfer(
            cpi_ctx.with_signer(gen_seeds!(self.escrow_state, vault_bump)),
            self.escrow_state.maker_amount,
        )
    }

    fn transfer_to_taker_native(&self, vault_bump: u8) -> ProgramResult {
        solana_program::program::invoke_signed(
            &solana_program::system_instruction::transfer(
                self.escrow_vault.key,
                // NOTE: Should be the same as self.taker
                self.to_taker_account.key,
                sol_to_lamports(self.escrow_state.maker_amount as f64),
            ),
            &[
                self.escrow_vault.to_account_info(),
                self.taker.to_account_info(),
                self.system_program.to_account_info()
            ],
            gen_seeds!(self.escrow_state, vault_bump),
        )
    }

    fn transfer_to_maker_token(&self, vault_bump: u8) -> ProgramResult {
        let cpi_accounts = Transfer {
            from: self.from_taker_account.to_account_info(),
            to: self.to_maker_account.to_account_info(),
            authority: self.taker.to_account_info(),
        };
        let cpi_program = self.token_program.to_account_info();
        let cpi_ctx = CpiContext::new(cpi_program, cpi_accounts);

        token::transfer(
            cpi_ctx.with_signer(gen_seeds!(self.escrow_state, vault_bump)),
            self.escrow_state.taker_amount,
        )
    }

    fn transfer_to_maker_native(&self) -> ProgramResult {
        solana_program::program::invoke(
            &solana_program::system_instruction::transfer(
                self.from_taker_account.key,
                self.to_maker_account.key,
                sol_to_lamports(self.escrow_state.taker_amount as f64),
            ),
            &[
                self.from_taker_account.to_account_info(),
                self.to_maker_account.to_account_info(),
                self.system_program.to_account_info()
            ],
        )
    }

    fn close_escrow_vault_token(&self, vault_bump: u8) -> ProgramResult {
        let cpi_accounts = anchor_spl::token::CloseAccount {
            account: self.escrow_vault.to_account_info(),
            destination: self.maker.to_account_info(),
            authority: self.escrow_vault.to_account_info(),
        };
        let cpi_program = self.token_program.to_account_info();
        let cpi_ctx = CpiContext::new(cpi_program, cpi_accounts);

        token::close_account(cpi_ctx.with_signer(gen_seeds!(self.escrow_state, vault_bump)))
    }

    fn close_escrow_vault_native(&self, vault_bump: u8) -> ProgramResult {
        solana_program::program::invoke_signed(
            &solana_program::system_instruction::transfer(
                self.escrow_vault.key,
                self.maker.key,
                self.escrow_vault.lamports(),
            ),
            &[
                self.escrow_vault.to_account_info(),
                self.maker.to_account_info(),
                self.system_program.to_account_info()
            ],
            gen_seeds!(self.escrow_state, vault_bump),
        )
    }
}
