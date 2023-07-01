import AMMLib.AMMSet
import AMMLib.State
import AMMLib.Supply

structure Deposit0 (s: Γ) where
  t0: 𝕋₀
  t1: 𝕋₀
  r0: ℝ+
  r1: ℝ+
  a: 𝔸
  hdif: t0 ≠ t1
  hnin: ¬s.amms.init t0 t1
  hen0: r0 ≤ s.atoms.get a t0
  hen1: r1 ≤ s.atoms.get a t1 

noncomputable def Deposit0.apply 
{s: Γ} (v: Deposit0 s): Γ :=
  ⟨
  (s.atoms.sub v.a v.t0 v.r0 v.hen0).sub v.a v.t1 v.r1 (by simp [v.hen1, v.hdif]),
  s.mints.add v.a v.t0 v.t1 v.hdif v.r0,
  s.amms.initialize v.hdif v.hnin v.r0 v.r1
  ⟩

@[simp] theorem Deposit0.supply_minted_diff 
{s: Γ} (v: Deposit0 s)
(t0 t1: 𝕋₀) (hdifp: diffpair v.t0 v.t1 t0 t1):
v.apply.mintsupply t0 t1 = s.mintsupply t0 t1 := by
  simp [apply, Γ.mintsupply, hdifp]

@[simp] theorem Deposit0.init_diff_iff
  {s: Γ} (v: Deposit0 s) (t0 t1: 𝕋₀) (hdifp: diffpair v.t0 v.t1 t0 t1):
  v.apply.amms.init t0 t1 ↔ s.amms.init t0 t1
  :=
  by sorry
