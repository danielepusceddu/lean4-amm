import Mathlib.Data.Finset.Basic
import «Helpers»
import «PReal»
import «PFun»
import «Tokens»

structure AMM where
  f: AtomicTok ⇀ ℝ+
  h: f.supp.card = 2

structure AtomicTokOf (a: AMM) where
  t: AtomicTok
  h: t ∈ a.f.supp

def AtomicTokOf.other {a: AMM} (t: AtomicTokOf a): 
  AtomicTokOf a :=
  ⟨Finset.other a.f.supp a.h t.t t.h,
   Finset.other_in a.f.supp a.h t.t t.h
  ⟩

def AMM.r0 (a: AMM) (t: AtomicTokOf a): ℝ+ :=
  a.f.fh t.t t.h

def AMM.r1 (a: AMM) (t: AtomicTokOf a): ℝ+ :=
  a.f.fh (t.other).t (t.other).h

lemma AMM.r0_other (a: AMM) (t: AtomicTokOf a):
  a.r0 (t.other) = a.r1 t := by simp [r0,r1]

def AMM.add 
  (a: AMM) (t: AtomicTokOf a) (val: ℝ+) 
  : AMM :=
  ⟨a.f.update t.t ((a.f.fh t.t t.h)+val),
   by simp [PFun.update]
      rw [Finset.card_insert_of_mem t.h]
      exact a.h⟩

lemma AMM.add_support (a: AMM) (t: AtomicTokOf a) (val: ℝ+) 
  : (a.add t val).f.supp = a.f.supp := by
  simp [add]; exact a.f.supp_of_update_mem t.t t.h val

def AtomicTokOf.ofAdd 
  {a: AMM} (t: AtomicTokOf a) (tadd: AtomicTokOf a) (val: ℝ+)
  : AtomicTokOf (a.add tadd val) :=
  ⟨t.t,
   by rw [a.add_support tadd val]; exact t.h
  ⟩

def AMM.sub
  (a: AMM) (t: AtomicTokOf a) (sub: ℝ+)
  (enough: sub < a.r0 t): AMM :=
  ⟨a.f.update t.t ((a.r0 t).sub sub enough),
   by simp [PFun.update]
      rw [Finset.card_insert_of_mem t.h]
      exact a.h⟩

lemma AMM.sub_support 
  (a: AMM) (t: AtomicTokOf a) 
  (val: ℝ+) (enough: val < a.r0 t)
  : (a.sub t val enough).f.supp = a.f.supp := by
  simp [add]; exact a.f.supp_of_update_mem t.t t.h val

def AtomicTokOf.ofSub 
  {a: AMM} (t: AtomicTokOf a) {tsub: AtomicTokOf a} {val: ℝ+}
  {enough: val < a.r0 tsub}
  : AtomicTokOf (a.sub tsub val enough) :=
  ⟨t.t,
   by rw [a.sub_support tsub val]; exact t.h
  ⟩

def AMM.SwapRate {a: AMM} := (AtomicTokOf a) → PReal → PReal

noncomputable def AMM.constprod {a: AMM}: @AMM.SwapRate a :=
  λ (t: AtomicTokOf a) (x: PReal) => a.r1 t / ((a.r0 t) + x)

def AMM.swap
  (a: AMM) (t: AtomicTokOf a) (sx: SwapRate) (v0: ℝ+)
  (nodrain: v0*(sx t v0) < a.r1 t)
  : AMM := 
  (a.sub t.other (v0*(sx t v0)) nodrain).add (t.ofSub) v0

def AtomicTok.ofSwap 
  {a: AMM} (t: AtomicTokOf a)
  (t0: AtomicTokOf a) (sx: AMM.SwapRate)
  (v0: ℝ+) (nodrain: v0*(sx t0 v0) < a.r1 t0)
  : AtomicTokOf (a.swap t0 sx v0 nodrain) :=
  ⟨t.t,
   let t'  := @AtomicTokOf.ofSub a t t0.other (v0*(sx t0 v0)) nodrain
   let t0' := @AtomicTokOf.ofSub a t0 t0.other (v0*(sx t0 v0)) nodrain
   let t'' := @AtomicTokOf.ofAdd _ t' t0' v0
   by have ht: t.t = t''.t := by aesop
      unfold AMM.swap 
      rw [ht]
      exact t''.h
  ⟩
