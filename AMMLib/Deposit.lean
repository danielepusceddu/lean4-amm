import AMMLib.AMMSet
import AMMLib.State
import AMMLib.Supply

structure Deposit0 (s: Γ) (t0 t1: T) (a: A) (r0 r1: ℝ+) where
  hdif: t0 ≠ t1
  hnin: ¬s.amms.init t0 t1
  hen0: r0 ≤ s.atoms.get a t0
  hen1: r1 ≤ s.atoms.get a t1 

noncomputable def Deposit0.apply 
{s: Γ} (v: Deposit0 s t0 t1 a r0 r1): Γ :=
  ⟨
  (s.atoms.sub a t0 r0 v.hen0).sub a t1 r1 (by simp [v.hen1, v.hdif]),
  s.mints.add a t0 t1 v.hdif r0,
  s.amms.initialize v.hdif r0 r1
  ⟩

@[simp] theorem Deposit0.supply_minted_diff 
{s: Γ} (v: Deposit0 s t0 t1 a r0 r1)
(t0' t1': T) (hdifp: diffmint t0 t1 t0' t1'):
v.apply.mintsupply t0' t1' = s.mintsupply t0' t1' := by
  simp [apply, Γ.mintsupply, hdifp]

@[simp] theorem Deposit0.init_diff_iff
  {s: Γ} (v: Deposit0 s t0 t1 a r0 r1) (t0' t1': T) (hdifp: diffmint t0 t1 t0' t1'):
  v.apply.amms.init t0' t1' ↔ s.amms.init t0' t1'
  :=
  by simp [apply, hdifp]

/-
Deposit gain v = v0 * (mintedsupp)/r0

v0 = v * rx0 = v0 * mintedsupp/r0 * r0/mintedsupp = v0 ok
v1 = v * rx1 = v0 * mintedsupp/r0 * r1/mintedsupp = v0*r1/r0
-/
structure Deposit (s: Γ) (a: A) (t0 t1: T) (v0: ℝ+) where
  exi: s.amms.init t0 t1
  possupp: 0 < s.mints.supply t0 t1
  hen0: v0 ≤ s.atoms.get a t0
  hen1: v0*(s.amms.r0 t0 t1 exi)/(s.mints.supply t0 t1) ≤ s.atoms.get a t1

noncomputable def Deposit.v (d: Deposit s a t0 t1 v0): PReal :=
  v0 * ((s.mints.supply t0 t1).toPReal d.possupp)/(s.amms.r0 t0 t1 d.exi)

noncomputable def Deposit.v1 (d: Deposit s a t0 t1 v0): PReal :=
  v0*(s.amms.r0 t0 t1 d.exi)/((s.mints.supply t0 t1).toPReal d.possupp)

noncomputable def Deposit.apply (d: Deposit s a t0 t1 v0): Γ :=
  ⟨
    s.atoms.sub a t0 v0 d.hen0,
    s.mints.add a t0 t1 d.exi.dif d.v,
    (s.amms.add_r0 t0 t1 d.exi v0).add_r1 t0 t1 (by simp[d.exi]) d.v1
  ⟩

@[simp] theorem Deposit.atoms (d: Deposit s a t0 t1 v0):
  d.apply.atoms = s.atoms.sub a t0 v0 d.hen0 := by simp [apply]

@[simp] theorem Deposit.mints (d: Deposit s a t0 t1 v0):
  d.apply.mints = s.mints.add a t0 t1 d.exi.dif d.v := by simp [apply]

@[simp] theorem Deposit.amms (d: Deposit s a t0 t1 v0):
  d.apply.amms = (s.amms.add_r0 t0 t1 d.exi v0).add_r1 t0 t1 (by simp[d.exi]) d.v1 
  := by simp [apply]