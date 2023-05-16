import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import «PReal»
open BigOperators

abbrev Account := ℕ
abbrev AtomicTok := ℕ

structure MintedTok where
  upair: Finset AtomicTok
  hcard: upair.card = 2

instance: DecidableEq MintedTok :=
  fun x y => 
  by rcases x with ⟨p1,h1⟩
     rcases y with ⟨p2,h2⟩
     simp
     infer_instance

inductive Token where
  | Atomic: AtomicTok → Token
  | Minted: MintedTok → Token
open Token

instance : Coe AtomicTok Token where
  coe := Atomic
instance : Coe MintedTok Token where
  coe := Minted

-- DecidableEq for Tokens
instance: DecidableEq Token := fun x y => by 
  rcases x with t1|m1
  . rcases y with t2|m2
    . simp; infer_instance
    . simp; infer_instance
  . rcases y with t2|m2
    . simp; infer_instance
    . simp; infer_instance

-- Wallets are functions defined everywhere,
-- but they're non-zero only on a finite set of tokens.
abbrev Wallet       := Token →₀ NNReal

-- DecidableEq for Wallets
noncomputable instance: DecidableEq Wallet := Finsupp.decidableEq
abbrev AccountSet   := Account →₀ Wallet
abbrev AtomicOracle  := AtomicTok → PReal

