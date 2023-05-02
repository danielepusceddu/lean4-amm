import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Basic
import «Helpers»
import «PReal»
import «Tokens»
open BigOperators

structure AMM where
  t0: AtomicTok
  t1: AtomicTok
  r0: PReal
  r1: PReal
  ht: t0 ≠ t1

def AMM.r (a: AMM) (t: AtomicTok) (h: t=a.t0 ∨ t=a.t1) :=
  match m1:Decidable.decide (t=a.t0) with
  | true => a.r0
  | false => match m2:Decidable.decide (t=a.t1) with
    | true => a.r1
    | false => nomatch (or_eq_contra t a.t0 a.t1 h m1 m2)

lemma AMM.r_eq_r0 (a: AMM) (t: AtomicTok) (h: t=a.t0)
  : a.r t (Or.intro_left (t=a.t1) h) = a.r0 := by
  simp [AMM.r]; split;
  next triv => rfl
  next cont => simp at cont; contradiction

lemma AMM.r_eq_r1 (a: AMM) (t: AtomicTok) (h: t=a.t1)
  : a.r t (Or.intro_right (t=a.t0) h) = a.r1 := by
  simp [AMM.r]; split;
  next cont => simp at cont; rw [h] at cont;
               have cont' := Ne.symm a.ht; simp at cont'; contradiction
  next ntri => 
    split; next triv' => simp
    next cont => simp at cont; contradiction

def AMM.add (a: AMM) (t: AtomicTok) (add: PReal) (h: t=a.t0 ∨ t=a.t1) :=
  if m1:Decidable.decide (t=a.t0)
  then AMM.mk a.t0 a.t1 (a.r0 + add) a.r1 a.ht
  else if m2:Decidable.decide (t=a.t1)
  then AMM.mk a.t0 a.t1 a.r0 (a.r1+add) a.ht
  else nomatch (or_eq_contra t a.t0 a.t1 h (eq_false_of_ne_true m1) (eq_false_of_ne_true m2))

def AMM.sub (a: AMM) (t: AtomicTok) (sub: PReal) (h: t=a.t0 ∨ t=a.t1)
            (enough: sub < a.r t h) :=
  if m1:Decidable.decide (t=a.t0)
  then AMM.mk a.t0 a.t1 (PReal.sub a.r0 sub 
       (by simp at m1; rw [AMM.r_eq_r0 a t m1] at enough; exact enough)
       ) a.r1 a.ht
  else if m2:Decidable.decide (t=a.t1)
  then AMM.mk a.t0 a.t1 a.r0 (PReal.sub a.r1 sub
       (by simp at m2; rw [AMM.r_eq_r1 a t m2] at enough; exact enough)
       ) a.ht
  else nomatch (or_eq_contra t a.t0 a.t1 h (eq_false_of_ne_true m1) (eq_false_of_ne_true m2))

lemma AMM.add.t0_same 
  {a: AMM} {t: AtomicTok} (add: PReal) (h: t=a.t0 ∨ t=a.t1)
  : a.t0 = (a.add t add h).t0 := by
  simp [AMM.add]; aesop

lemma AMM.add.t1_same 
  {a: AMM} {t: AtomicTok} (add: PReal) (h: t=a.t0 ∨ t=a.t1)
  : a.t1 = (a.add t add h).t1 := by
  simp [AMM.add]; aesop

lemma AMM.sub.t0_same 
  {a: AMM} {t: AtomicTok} {sub: PReal} (h: t=a.t0 ∨ t=a.t1)
  (enough: sub < a.r t h)
  : a.t0 = (a.sub t sub h enough).t0 := by
  simp [AMM.sub]; aesop

lemma AMM.sub.t1_same 
  {a: AMM} {t: AtomicTok} {sub: PReal} (h: t=a.t0 ∨ t=a.t1)
  (enough: sub < a.r t h)
  : a.t1 = (a.sub t sub h enough).t1 := by
  simp [AMM.sub]; aesop

lemma AMM.sub.still_belongs
  {a: AMM} {t: AtomicTok} {sub: PReal}
  (h: t=a.t0 ∨ t=a.t1) (enough: sub < a.r t h)
  (t': AtomicTok)  (h': t'=a.t0 ∨ t'=a.t1)
  : t' = (a.sub t sub h enough).t0 ∨ t' = (a.sub t sub h enough).t1 := by
  have h'': t' = (a.sub t sub h enough).t0 ∨ t' = a.t1 := 
    by rw [AMM.sub.t0_same h enough] at h'; exact h'
  rw [AMM.sub.t1_same h enough] at h''
  exact h''