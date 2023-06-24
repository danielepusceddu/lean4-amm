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
  hnin: s.amms.uninit t0 t1
  hen0: (s.atoms a) t0 ≤ r0
  hen1: (s.atoms a) t1 ≤ r1 

noncomputable def Deposit0.apply 
{s: Γ} (v: Deposit0 s): Γ :=
  ⟨
  (s.atoms.subb v.a v.t0 v.r0).subb v.a v.t1 v.r1,
  s.mints.addb v.a (𝕋₀.toMint v.hdif) v.r0,

  s.amms.initialize v.hdif v.hnin v.r0 v.r1
  ⟩

@[simp] theorem Deposit0.supply_minted_diff 
{s: Γ} (v: Deposit0 s)
(m: 𝕋₁) (hdif: m ≠ (𝕋₀.toMint v.hdif)):
v.apply.mintsupply m = s.mintsupply m := by
  simp [apply, Γ.mintsupply, 𝕊₁.addb, hdif]

@[simp] theorem Deposit0.init_diff_iff
  {s: Γ} (v: Deposit0 s) (t0 t1: 𝕋₀)
  {hdif: t0 ≠ t1} (hdif': 𝕋₀.toMint hdif ≠ 𝕋₀.toMint v.hdif):
  v.apply.amms.init t0 t1 ↔ s.amms.init t0 t1
  :=
  by sorry

@[simp] theorem Deposit0.diff_same 
{s: Γ} (v: Deposit0 s)
(t0 t1: 𝕋₀) (hdif: (t0 ≠ v.t0 ∨ t1 ≠ v.t1) ∧ (t0 ≠ v.t1 ∨ t1 ≠ v.t0)):
v.apply.amms.f t0 t1 = s.amms.f t0 t1 := by
  simp [apply, hdif]
  sorry