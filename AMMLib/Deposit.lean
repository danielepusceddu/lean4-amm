import AMMLib.AMMSet
import AMMLib.State
import AMMLib.Supply

structure Deposit0 (s: State) where
  t0: AtomicTok
  t1: AtomicTok
  r0: ℝ+
  r1: ℝ+
  a: Account
  hdif: t0 ≠ t1
  hnin: s.amms.f t0 t1 = (0,0)
  hen0: (s.atoms a) t0 ≤ r0
  hen1: (s.atoms a) t1 ≤ r1 

noncomputable def Deposit0.apply 
{s: State} (v: Deposit0 s): State :=
  ⟨
  (s.atoms.subb v.a v.t0 v.r0).subb v.a v.t1 v.r1,
  s.mints.addb v.a (AtomicTok.toMint v.hdif) v.r0,
  s.amms.up v.t0 v.t1 (v.r0, v.r1) v.hdif (by sorry)
  ⟩

@[simp] theorem Deposit0.supply_minted_diff 
{s: State} (v: Deposit0 s)
(m: MintedTok) (hdif: m ≠ (AtomicTok.toMint v.hdif)):
v.apply.mintsupply m = s.mintsupply m := by
  simp [apply, State.mintsupply, MintedWalls.addb, hdif]

@[simp] theorem Deposit0.diff_same 
{s: State} (v: Deposit0 s)
(t0 t1: AtomicTok) (hdif: (t0 ≠ v.t0 ∨ t1 ≠ v.t1) ∧ (t0 ≠ v.t1 ∨ t1 ≠ v.t0)):
v.apply.amms.f t0 t1 = s.amms.f t0 t1 := by
  simp [apply, hdif]