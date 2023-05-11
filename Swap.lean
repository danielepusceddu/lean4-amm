import «Tokens»
import «AMM»
import «AMMSet»
import «State»

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

noncomputable def Wallet.swap (w: Wallet) (amm: AMM)
  (t0: AtomicOf amm) (v0: ℝ+) (sx: @AMM.SwapRate amm)
  (_: w t0.t ≤ v0): Wallet :=
  (w.update t0.t ((w t0.t) - v0.toNNReal)).update t0.other.t ((w t0.other.t) + v0*(sx t0 v0))

structure Swap.Valid (c: Config) (s: State) where
  m: MintedOf s.amms
  t0: AtomicOfM m
  a: Account
  v0: ℝ+
  enough: v0 ≤ s.accs a t0.t
  nodrain: v0*(c.sx t0.ofAMM v0) < m.amm.r1 t0.ofAMM

noncomputable def Swap.apply (sw: Valid c s): State :=
⟨
    s.accs.update sw.a ((s.accs sw.a).update sw.t0.t (((s.accs sw.a) sw.t0.t) - sw.v0.toNNReal)),
    s.amms.update (sw.m.amm.swap sw.t0.ofAMM c.sx sw.v0 sw.nodrain)
⟩