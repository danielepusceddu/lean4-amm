# Automated Market Makers in the Lean 4 Theorem Prover
This repository contains a formalization of Automated Market Makers in the Lean 4 Theorem Prover. The formalization is based on the work of Bartoletti, Chiang and Lluch-Lafuente in *A theory of Automated Market Makers in DeFi*.

## State definitions and properties
In [AMMLib/State](AMMLib/State) we give the fundamental definitions to model the state of a system of AMMs as well as to model several properties of a state, such as the price and the supply of minted tokens.
### Tokens and accounts
[Token.lean](AMMLib/State/Token.lean) contains definitions for the two most basic underlying types: `Account` and `Token`. Both are defined as wrappers to the natural numbers, which renders equality decidable.
### Wallets
Wallets are split into two types.
- [AtomicWall.lean](AMMLib/State/AtomicWall.lean) contains definitions for wallets of atomic token types `W₀`. They are modeled as finitely supported functions from `Token` to non-negative reals.
- [MintedWall.lean](AMMLib/State/MintedWall.lean) contains definitions for wallets of minted token types `W₁`. They are modeled as constrained finitely supported functions from pairs of `Token` to non-negative reals.
Then, [AtomicWallSet.lean](AMMLib/State/AtomicWallSet.lean) and [MintedWallSet.lean](AMMLib/State/MintedWallSet.lean) define sets of atomic token wallets `S₀` and sets of minted token wallets `S₁` as finitely supported functions from `Account` to `W₀` and from `Account` to `W₁` respectively.
### Automated Market Makers
We do not define a type for a singular AMM, instead we directly define sets of AMMs `AMMs` in [AMMs.lean](AMMLib/State/AMMs.lean). Similarly to minted token type wallets, they are modeled as constrained finitely supported functions from pairs of `Token` to non-negative reals. The constraints on a set `f` of AMMs are:
- `f t0 t1 ≠ 0 ↔ f t1 t0 ≠ 0`
- `f t t = 0`
The intuition is that `f t0 t1` and `f t1 t0` will be the amount of token `t0` and of token `t1` respectively in the liquidity pool of the `t0` - `t1` decentralized exchange.
### State
In [State.lean](AMMLib/State/State.lean) we define the state type `Γ` as a triple of sets of atomic type wallets, sets of minted type wallets and sets of AMMs. In [Networth.lean](AMMLib/State/Networth.lean) we define the price of a unit of a minted token type and the wealth of a user. In [Supply.lean](AMMLib/State/Supply.lean) we define the supply of tokens in a state.
## Transactions
In [AMMLib/Transaction](AMMLib/Transaction) we define the various types of transactions and prove some of their effects on the state and on the users' wealth, giving particular attention to the swap transaction, to which we dedicate multiple files in the [Swap](AMMLib/Transaction/Swap) directory. There we define several properties a swap rate function may have and their consequences on the results of the swap transactions. In [Constprod.lean](AMMLib/Transaction/Swap/Constprod.lean) we define the constant product swap rate function and prove some of its properties and economic features. 

## Reachable States
In [Trace.lean](AMMLib/Transaction/Trace.lean) we define valid sequences of transactions starting from a state, which we use to define reachable states as valid sequences of transactions starting from the initial state. We then prove that the existence of an AMM Implies the circulation of its associated minted token type.
