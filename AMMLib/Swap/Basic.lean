import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.State
import AMMLib.Supply

structure Swap 
  (sx: SX) (o: 𝕆) (s: Γ) (a: 𝔸) (t0 t1: 𝕋) (v0: ℝ+) 
  where
  enough: v0 ≤ s.atoms.get a t0
  exi: s.amms.init t0 t1
  nodrain: v0*(sx v0 (s.amms.r0 t0 t1 exi) (s.amms.r1 t0 t1 exi)) < (s.amms.r1 t0 t1 exi)

def Swap.rate (sw: Swap sx o s a t0 t1 v0): ℝ+
  := sx v0 (s.amms.r0 t0 t1 sw.exi) (s.amms.r1 t0 t1 sw.exi)
  
def Swap.y (sw: Swap sx o s a t0 t1 v0): ℝ+
  := v0*sw.rate


/-
def Swap.hdif (sw: Swap sx o s a t0 t1 v0):
t0 ≠ t1 := 𝕊ₐ.exists_imp_dif sw.exi

def Swap.mint (sw: Swap sx o s a t0 t1 v0)
: 𝕋₁ := 𝕋.toMint sw.hdif

def Swap.exi_swap (sw: Swap sx o s a t0 t1 v0):
  s.amms.f t1 t0 ≠ 0 :=
    𝕊ₐ.exists_swap sw.exi
-/

noncomputable def Swap.apply (sw: Swap sx o s a t0 t1 v0): Γ :=
⟨
  (s.atoms.sub a t0 v0 sw.enough).add a t1 sw.y,
  s.mints,
  (s.amms.sub_r1 t0 t1 sw.exi sw.y sw.nodrain).add_r0 t0 t1 (by simp[sw.exi]) v0
⟩

@[simp] theorem 𝕊ₐ.init_of_swap (sw: Swap sx o s a t0 t1 v0)
  (t0' t1': 𝕋):
  sw.apply.amms.init t0' t1' ↔ s.amms.init t0' t1' := by
    unfold Swap.apply
    simp

@[simp] theorem Swap.r0_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).amms.r0 t0 t1 (by simp[sw.exi]) = v0 + s.amms.r0 t0 t1 sw.exi := by 
  unfold apply;
  simp [sw.exi]

@[simp] theorem Swap.r1_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).amms.r1 t0 t1 (by simp[sw.exi]) = (s.amms.r1 t0 t1 sw.exi).sub sw.y (sw.nodrain) := by 
  unfold apply;
  simp [sw.exi]

@[simp] theorem Swap.atoms_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).atoms.get a = ((s.atoms.get a).sub t0 v0 sw.enough).add t1 sw.y := by simp [apply]

@[simp] theorem Swap.atoms_diff
  (sw: Swap sx o s a t0 t1 v0) (a': 𝔸) (hdif: a ≠ a'):
  (sw.apply).atoms.get a' = s.atoms.get a' := by simp [apply, hdif]

@[simp] theorem Swap.b0_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).atoms.get a t0 = s.atoms.get a t0 - v0 := by
  unfold apply
  simp [sw.exi.dif, sw.exi.dif, sw.exi.dif.symm]

@[simp] theorem Swap.b1_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).atoms.get a t1 = s.atoms.get a t1 + sw.y := by
  unfold apply
  simp [sw.exi.dif.symm, sw.exi.dif]

@[simp] theorem Swap.init_iff
  (sw: Swap sx o s a t0 t1 v0)
  (t0' t1': 𝕋):
  sw.apply.amms.init t0' t1' ↔ s.amms.init t0' t1' := by
  unfold apply
  simp

@[simp] theorem Swap.mints_eq
  (sw: Swap sx o s a t0 t1 v0):
  sw.apply.mints = s.mints := by simp [apply]

@[simp] theorem Swap.r0_diff
  (sw: Swap sx o s a t0 t1 v0)
  (t0' t1': 𝕋) (init: s.amms.init t0' t1')
  (hdif: diffmint t0 t1 t0' t1'):
  (sw.apply).amms.r0 t0' t1' (by simp[init]) = s.amms.r0 t0' t1' init := by 
  unfold apply;
  simp [sw.exi, init, hdif]

@[simp] theorem Swap.r1_diff
  (sw: Swap sx o s a t0 t1 v0)
  (t0' t1': 𝕋) (init: s.amms.init t0' t1')
  (hdif: diffmint t0 t1 t0' t1'):
  (sw.apply).amms.r1 t0' t1' (by simp[init]) = s.amms.r1 t0' t1' init := by 
  unfold apply;
  simp [sw.exi, init, hdif]

@[simp] theorem Swap.drain_atoms
  (sw: Swap sx o s a t0 t1 v0) (a': 𝔸):
  ((sw.apply.atoms.get a').drain t0).drain t1 = ((s.atoms.get a').drain t0).drain t1 := by 
  unfold apply;
  rcases Decidable.em (a=a') with eq|neq
  . rw [𝕎₀.drain_comm]; 
    simp only [eq, 𝕊₀.get_add_self, 𝕊₀.get_sub_self, 𝕎₀.drain_add_self, ne_eq]
    rw [𝕎₀.drain_comm]
    simp
  . simp [neq]

def Swap.inv 
  (sw: Swap sx o s a t0 t1 v0)
  (hbound: SX.outputbound sx)
  (hrev: SX.reversible sx hbound)
  : Swap sx o sw.apply a t1 t0 sw.y
  :=
  ⟨
    by simp,
    by simp [sw.exi.swap],
    by 
      unfold SX.outputbound at hbound
      unfold SX.reversible at hrev
      rw [𝕊ₐ.r0_reorder _ t1 t0, 𝕊ₐ.r1_reorder _ t1 t0]
      simp [hrev, y, rate]
  ⟩

theorem Swap.inv_y_eq_x
  (sw: Swap sx o s a t0 t1 x)
  (hbound: SX.outputbound sx)
  (hrev: SX.reversible sx hbound)
  : (sw.inv hbound hrev).y = x := by 
  unfold y
  unfold rate
  rw [𝕊ₐ.r0_reorder _ t1 t0 _,
      𝕊ₐ.r1_reorder _ t1 t0 _]
  rw [mul_assoc]
  unfold SX.reversible at hrev
  simp [y, rate, hrev]

@[simp] theorem Swap.mintsupply
  (sw: Swap sx o s a t0 t1 v0)
  (t0' t1': 𝕋): 
  sw.apply.mintsupply t0' t1' = s.mintsupply t0' t1' := by
  simp [Swap.apply, Γ.mintsupply]
