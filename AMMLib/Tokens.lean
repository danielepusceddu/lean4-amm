import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finsupp.Basic
import AMMLib.PReal
import AMMLib.Helpers
import AMMLib.Finsupp2
open BigOperators

structure Account where
  n: ℕ

abbrev AtomicTok := ℕ

instance: DecidableEq Account := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

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



abbrev AtomicWalls := Account →₀ AtomicTok →₀ NNReal
abbrev MintedWalls := Account →₀ MintedTok →₀ NNReal
abbrev AtomicOracle  := AtomicTok → PReal

noncomputable def AtomicWalls.addb (as: AtomicWalls) (a: Account) (t: AtomicTok) (v: NNReal)
  : AtomicWalls := as.up a t ((as a t) + v)

noncomputable def AtomicWalls.subb (as: AtomicWalls) (a: Account) (t: AtomicTok) (v: NNReal)
  : AtomicWalls := as.up a t ((as a t) - v)

noncomputable def MintedWalls.addb (as: MintedWalls) (a: Account) (t: MintedTok) (v: NNReal)
  : MintedWalls := as.up a t ((as a t) + v)

noncomputable def MintedWalls.subb (as: MintedWalls) (a: Account) (t: MintedTok) (v: NNReal)
  : MintedWalls := as.up a t ((as a t) - v)