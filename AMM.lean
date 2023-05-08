import Mathlib.Data.Finset.Basic
import «Helpers»
import «PReal»
import «PFun»
import «Tokens»

structure AMM where
  f: AtomicTok ⇀ ℝ+
  h: f.supp.card = 2

def AMM.toMint (a: AMM): MintedTok :=
  ⟨a.f.supp, a.h⟩

structure AtomicOf (a: AMM) where
  t: AtomicTok
  h: t ∈ a.f.supp

def AtomicOf.other {a: AMM} (t: AtomicOf a): 
  AtomicOf a :=
  ⟨Finset.other a.f.supp a.h t.t t.h,
   Finset.other_in a.f.supp a.h t.t t.h
  ⟩

theorem AtomicOf.other_inv  {a: AMM} (t: AtomicOf a): 
  t.other.other = t :=
  by rcases t with ⟨atom,h⟩
     simp [other]
     exact Finset.other_inv a.f.supp a.h atom h

lemma AtomicOf.other.diff 
  {a: AMM} (t: AtomicOf a)
  : t.t ≠ t.other.t := by 
    apply Ne.symm
    simp [other]
    exact Finset.other_diff a.f.supp a.h t.t t.h

def AMM.r0 (a: AMM) (t: AtomicOf a): ℝ+ :=
  a.f.fh t.t t.h

def AMM.r1 (a: AMM) (t: AtomicOf a): ℝ+ :=
  a.f.fh (t.other).t (t.other).h

lemma AMM.r0_other (a: AMM) (t: AtomicOf a):
  a.r0 (t.other) = a.r1 t := by simp [r0,r1]

lemma AMM.r1_other (a: AMM) (t: AtomicOf a):
  a.r1 (t.other) = a.r0 t := by 
  rw [← AMM.r0_other]
  rw [AtomicOf.other_inv]

def AMM.add 
  (a: AMM) (t: AtomicOf a) (val: ℝ+) 
  : AMM :=
  ⟨a.f.update t.t ((a.f.fh t.t t.h)+val),
   by simp [PFun.update]
      rw [Finset.card_insert_of_mem t.h]
      exact a.h⟩

lemma AMM.add_support (a: AMM) (t: AtomicOf a) (val: ℝ+) 
  : (a.add t val).f.supp = a.f.supp := by
  simp [add]; exact a.f.supp_of_update_mem t.t t.h val

def AtomicOf.ofAdd 
  {a: AMM} (t: AtomicOf a) (tadd: AtomicOf a) (val: ℝ+)
  : AtomicOf (a.add tadd val) :=
  ⟨t.t,
   by rw [a.add_support tadd val]; exact t.h
  ⟩

lemma AtomicOf.otherOfAdd
  {a: AMM} (t: AtomicOf a) (tadd: AtomicOf a) (val: ℝ+)
  : (t.ofAdd tadd val).other = t.other.ofAdd tadd val := by
  simp [other, ofAdd]; 
  conv in (AMM.add _ _ _).f.supp => rw [AMM.add_support]

/-
T
1: a.r0 t = a.r1 t.other
2: a.r1 t = a.r0 t.other

BASE
3: (a.add t v).r0 t = a.r0 t + v
4: (a.add t v).r1 t = a.r1 t

USING T AND BASE
(a.add t v).r0 t.other = (a.add t v).r1 t   by 2
(a.add t v).r1 t.other = (a.add t v).r0 t   by 1
(a.add t.other v).r0 t = (a.add t.other v).r1 t.other
(a.add t.other v).r1 t = (a.add t.other v).r0 t.other
-/

def AMM.r0_add_self 
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+)
  : (a.add t val).r0 (t.ofAdd t val)
    =
    a.r0 t + val
  := by simp [AMM.add, AtomicOf.ofAdd, r0, PFun.update, PFun.fh]
        aesop

-- This proof should become better by
-- adding simp rules about .t equality
def AMM.r1_add_self 
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+)
  : (a.add t val).r1 (t.ofAdd t val)
    =
    a.r1 t
  := by 
  unfold r1
  unfold add
  simp
  rw [PFun.update_fh_of_diff]
  . conv in (AtomicOf.other _).t => 
      rw [AtomicOf.otherOfAdd]
      simp [AtomicOf.ofAdd]
  . rw [AtomicOf.otherOfAdd]
    simp [AtomicOf.ofAdd]
    exact AtomicOf.other.diff t
  . simp [AtomicOf.otherOfAdd]
    simp [AtomicOf.ofAdd]
    exact (AtomicOf.other t).h

lemma AMM.r0_other_add_self 
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+)
  : (a.add t val).r0 (t.other.ofAdd t val)
    =
    a.r1 t := by
  rw [← AtomicOf.otherOfAdd]
  rw [AMM.r0_other]
  rw [AMM.r1_add_self]

lemma AMM.r1_other_add_self 
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+)
  : (a.add t val).r1 (t.other.ofAdd t val)
    =
    a.r0 t + val := by
  rw [← AtomicOf.otherOfAdd]
  rw [AMM.r1_other]
  rw [AMM.r0_add_self]

lemma AMM.r0_self_add_other
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+)
  : (a.add t.other val).r0 (t.ofAdd t.other val)
    =
    a.r0 t := by
  rw [← AMM.r1_other]
  rw [AtomicOf.otherOfAdd]
  rw [AMM.r1_add_self]
  rw [AMM.r1_other]

lemma AMM.r1_self_add_other
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+)
  : (a.add t.other val).r1 (t.ofAdd t.other val)
    =
    a.r1 t + val := by
    rw [← AMM.r0_other]
    rw [AtomicOf.otherOfAdd]
    rw [AMM.r0_add_self]
    rw [AMM.r0_other]

def AMM.sub
  (a: AMM) (t: AtomicOf a) (sub: ℝ+)
  (enough: sub < a.r0 t): AMM :=
  ⟨a.f.update t.t ((a.r0 t).sub sub enough),
   by simp [PFun.update]
      rw [Finset.card_insert_of_mem t.h]
      exact a.h⟩

lemma AMM.sub_support 
  (a: AMM) (t: AtomicOf a) 
  (val: ℝ+) (enough: val < a.r0 t)
  : (a.sub t val enough).f.supp = a.f.supp := by
  simp [add]; exact a.f.supp_of_update_mem t.t t.h val

def AtomicOf.ofSub 
  {a: AMM} (t: AtomicOf a) {tsub: AtomicOf a} {val: ℝ+}
  {enough: val < a.r0 tsub}
  : AtomicOf (a.sub tsub val enough) :=
  ⟨t.t,
   by rw [a.sub_support tsub val]; exact t.h
  ⟩

lemma AtomicOf.otherOfSub
  {a: AMM} (t: AtomicOf a) (tsub: AtomicOf a) (val: ℝ+)
  (enough: val < a.r0 tsub)
  : (@AtomicOf.ofSub a t tsub val enough).other = t.other.ofSub := by
  simp [other, ofAdd]; 
  conv in (AMM.sub _ _ _ _).f.supp => rw [AMM.sub_support]

lemma AMM.r0_sub_self 
  {a: AMM} (t: AtomicOf a)
  (sub: ℝ+) (enough: sub < a.r0 t)
  : (a.sub t sub enough).r0 t.ofSub
    =
    (a.r0 t).sub sub enough
  := by simp [AMM.sub, AtomicOf.ofSub, r0, PFun.update, PFun.fh]
        aesop

lemma AMM.r1_sub_self 
  {a: AMM} (t: AtomicOf a)
  (sub: ℝ+) (enough: sub < a.r0 t)
  : (a.sub t sub enough).r1 t.ofSub
    =
    a.r1 t
  := by 
  unfold r1
  unfold sub
  simp
  rw [PFun.update_fh_of_diff]
  . conv in (AtomicOf.other _).t => 
      rw [AtomicOf.otherOfSub]
      simp [AtomicOf.ofAdd]
  . rw [AtomicOf.otherOfSub]
    simp [AtomicOf.ofSub]
    exact AtomicOf.other.diff t
  . simp [AtomicOf.otherOfSub]
    simp [AtomicOf.ofSub]
    exact (AtomicOf.other t).h

lemma AMM.r0_other_sub_self 
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+) (enough: val < a.r0 t)
  : (a.sub t val enough).r0 t.other.ofSub
    =
    a.r1 t := by
  rw [← AtomicOf.otherOfSub]
  rw [AMM.r0_other]
  rw [AMM.r1_sub_self]

lemma AMM.r1_other_sub_self 
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+) (enough: val < a.r0 t)
  : (a.sub t val enough).r1 t.other.ofSub
    =
    (a.r0 t).sub val enough := by
  rw [← AtomicOf.otherOfSub]
  rw [AMM.r1_other]
  rw [AMM.r0_sub_self]

lemma AMM.r0_self_sub_other
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+) (enough: val < a.r0 t.other)
  : (a.sub t.other val enough).r0 t.ofSub
    =
    a.r0 t := by
  rw [← AMM.r1_other]
  rw [AtomicOf.otherOfSub]
  rw [AMM.r1_sub_self]
  rw [AMM.r1_other]

lemma AMM.r1_self_sub_other
  {a: AMM} (t: AtomicOf a)
  (val: ℝ+) (enough: val < a.r0 t.other)
  : (a.sub t.other val enough).r1 t.ofSub
    =
    (a.r1 t).sub val enough := by
    rw [← AMM.r0_other]
    rw [AtomicOf.otherOfSub]
    rw [AMM.r0_sub_self]
    simp_rw [AMM.r0_other]

def AMM.SwapRate {a: AMM} := (AtomicOf a) → PReal → PReal

noncomputable def AMM.constprod {a: AMM}: @AMM.SwapRate a :=
  λ (t: AtomicOf a) (x: PReal) => a.r1 t / ((a.r0 t) + x)

def AMM.swap
  (a: AMM) (t: AtomicOf a) (sx: SwapRate) (v0: ℝ+)
  (nodrain: v0*(sx t v0) < a.r1 t)
  : AMM := 
  (a.sub t.other (v0*(sx t v0)) nodrain).add (t.ofSub) v0

def AtomicOf.ofSwap 
  {a: AMM} (t: AtomicOf a)
  (t0: AtomicOf a) (sx: AMM.SwapRate)
  (v0: ℝ+) (nodrain: v0*(sx t0 v0) < a.r1 t0)
  : AtomicOf (a.swap t0 sx v0 nodrain) :=
  ⟨t.t,
   let t'  := @AtomicOf.ofSub a t t0.other (v0*(sx t0 v0)) nodrain
   let t0' := @AtomicOf.ofSub a t0 t0.other (v0*(sx t0 v0)) nodrain
   let t'' := @AtomicOf.ofAdd _ t' t0' v0
   by have ht: t.t = t''.t := by aesop
      unfold AMM.swap 
      rw [ht]
      exact t''.h
  ⟩

lemma AtomicOf.ofSwap_def 
  {a: AMM} (t: AtomicOf a)
  (t0: AtomicOf a) (sx: AMM.SwapRate)
  (v0: ℝ+) (nodrain: v0*(sx t0 v0) < a.r1 t0)
  : t.ofSwap t0 sx v0 nodrain
    =
    (@AtomicOf.ofSub _ t _ _ nodrain).ofAdd (@AtomicOf.ofSub _ t0 _ _ nodrain) v0
  := by
  unfold ofSwap ofAdd ofSub; aesop

lemma AMM.r0_of_swap  
  (a: AMM) (t: AtomicOf a) (sx: SwapRate) (v0: ℝ+)
  (nodrain: v0*(sx t v0) < a.r1 t)
  : (a.swap t sx v0 nodrain).r0 (t.ofSwap t sx v0 nodrain) 
    = 
    (a.r0 t) + v0 := by 
  simp [swap, AtomicOf.ofSwap_def]
  rw [AMM.r0_add_self]
  rw [AMM.r0_self_sub_other]

lemma AMM.r1_of_swap  
  (a: AMM) (t: AtomicOf a) (sx: SwapRate) (v0: ℝ+)
  (nodrain: v0*(sx t v0) < a.r1 t)
  : (a.swap t sx v0 nodrain).r1 (t.ofSwap t sx v0 nodrain) 
    = 
    (a.r1 t).sub (v0*(sx t v0)) nodrain := by 
  simp [swap, AtomicOf.ofSwap_def]
  rw [AMM.r1_add_self]
  rw [AMM.r1_self_sub_other]

theorem AMM.constprod_def  {a: AMM} (t0: AtomicOf a) 
  (v0: ℝ+) (nodrain: v0*(AMM.constprod t0 v0) < a.r1 t0)
  : (a.r0 t0)*(a.r1 t0) = 
  ((a.swap t0 AMM.constprod v0 nodrain).r0 (AtomicOf.ofSwap t0 t0 AMM.constprod v0 nodrain))
  *
  ((a.swap t0 AMM.constprod v0 nodrain).r1 (AtomicOf.ofSwap t0 t0 AMM.constprod v0 nodrain))
  := by
  -- Coerce everything to ℝ
  apply (PReal.eq_iff _ _).mp
  repeat rw [PReal.coe_mul _ _]
  rw [AMM.r0_of_swap, AMM.r1_of_swap]
  rw [PReal.coe_add _ _, PReal.coe_sub, PReal.coe_mul]
  unfold constprod; rw [PReal.coe_div]
  have h := PReal.coe_pos (r0 a t0 + v0)
  rewrite [PReal.coe_add]; rw [PReal.coe_add] at h
  have h' := (GT.gt.ne _ _ h)

  -- Solve the equation
  field_simp; linarith