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

/- AccountSet as a map from tokens to accounts to balances
   The different order of the parameters may
   be useful: see Supply for an example. -/
def AccountSet.rev (as: AccountSet) (t: Token) (a: Account)
: NNReal := as a t

/- Given an AccountSet that was just updated,
   the maps for all other tokens remain the same. -/
lemma AccountSet.rev_update_diff (as: AccountSet) (t: Token) (a: Account) 
  (t': Token) (a': Account) (v: NNReal) (hdif: t ≠ t'):
  AccountSet.rev (as.update a' ((as a').update t' v)) t a = as.rev t a := by 
  unfold AccountSet.rev
  apply @Decidable.byCases (a=a')
  . intro heq
    simp [heq, hdif]
  . intro hneq
    simp [hneq]

/- If an account is not in the AccountSet's, then all of its
   balances will be zero. -/
lemma AccountSet.rev_account_not_mem (as: AccountSet) (t: Token) (a: Account):
  a ∉ as.support → as.rev t a = 0 := by
  intro h; unfold AccountSet.rev;
  rw [Finsupp.not_mem_support_iff] at h
  rw [h]; simp
  