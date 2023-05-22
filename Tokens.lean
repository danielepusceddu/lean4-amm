import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finsupp.Basic
import «PReal»
import «Helpers»
import «Finsupp2»
open BigOperators

abbrev Account := ℕ
abbrev AtomicTok := ℕ

structure MintedTok where
  upair: Sym2 AtomicTok
  hdiff: ¬Sym2.IsDiag upair

def AtomicTok.toMint
{t0 t1: AtomicTok} (hdif: t0 ≠ t1): MintedTok :=
⟨
  Quotient.mk (Sym2.Rel.setoid AtomicTok) (t0, t1),
  by simp [hdif]
⟩

noncomputable def MintedTok.choose (m: MintedTok)
: AtomicTok
:= (Quotient.out m.upair).fst

theorem MintedTok.choose_in (m: MintedTok)
: m.choose ∈ m.upair := by
unfold choose; exact Sym2.out_fst_mem m.upair

noncomputable def MintedTok.other (m: MintedTok)
: AtomicTok
:= Sym2.Mem.other (MintedTok.choose_in m)

theorem MintedTok.other_diff (m: MintedTok)
: m.choose ≠ m.other := by
unfold other
exact (Sym2.other_ne m.hdiff m.choose_in).symm

theorem MintedTok.eq_iff 
(m1: MintedTok) (m2: MintedTok)
: m1 = m2 ↔ m1.upair = m2.upair := by
apply Iff.intro
. intro h; simp [h]
. intro h; cases m1; cases m2; simp at h; simp [h]

@[simp] theorem MintedTok.choose_eq (m: MintedTok)
: AtomicTok.toMint (m.other_diff) = m := by
simp [AtomicTok.toMint]
apply (MintedTok.eq_iff _ _).mpr
simp [choose, other]

instance: DecidableEq MintedTok :=
  fun x y => 
  by rcases x with ⟨p1,h1⟩
     rcases y with ⟨p2,h2⟩
     simp
     infer_instance

theorem AtomicTok.toMint_diff 
{t0 t1 t0' t1': AtomicTok}
{hdif1: t0 ≠ t1}
{hdif2: t0' ≠ t1'}
(hdif3: AtomicTok.toMint hdif1 ≠ AtomicTok.toMint hdif2)
: (t0 ≠ t0' ∨ t1 ≠ t1') ∧ (t0 ≠ t1' ∨ t1 ≠ t0') := by
  simp [AtomicTok.toMint, hdif1, hdif2] at hdif3
  rcases (not_or.mp hdif3) with ⟨left, right⟩
  have left' := not_and_or.mp left
  have right' := not_and_or.mp right
  exact And.intro left' right'

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

noncomputable def AccountSet.addb (as: AccountSet) (a: Account) (t: Token) (v: NNReal)
  : AccountSet := as.up a t ((as a t) + v)

noncomputable def AccountSet.subb (as: AccountSet) (a: Account) (t: Token) (v: NNReal)
  : AccountSet := as.up a t ((as a t) - v)


def Token.isMinted (t: Token) := match t with
  | Token.Atomic _ => false
  | Token.Minted _ => true

def Token.getMinted (t: Token) (h: t.isMinted)
: MintedTok := match t with
| Token.Atomic _ => nomatch ((by simp [isMinted] at h): False)
| Token.Minted m => m