import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.State
import AMMLib.Supply

structure Swap (c: Config) (s: State) where
  t0: AtomicTok
  t1: AtomicTok
  a: Account
  v0: ℝ+
  enough: v0 ≤ s.accs a t0
  exi:    s.amms.f t0 t1 ≠ 0
  nodrain: v0*(c.sx v0 (s.amms.fp exi)) < (s.amms.f t0 t1).snd

noncomputable def Swap.apply (sw: Swap c s): State :=
⟨
  (s.atoms.addb sw.a sw.t1 (sw.v0*(c.sx sw.v0 (s.amms.fp sw.exi)))).subb sw.a sw.t0 sw.v0,
  s.mints,
  @AMMSet.sub_r1 (s.amms.add_r0 sw.v0 sw.exi) sw.t0 sw.t1 (sw.v0*(c.sx sw.v0 (s.amms.fp sw.exi))) (by sorry)
⟩

-- If an AMM is in the swap, then it was there before too.
theorem Swap.amm_in_apply 
{sw: Swap c s} {t0 t1: AtomicTok}
(h1: sw.apply.amms.f t0 t1 ≠ 0)
: s.amms.f t0 t1 ≠ 0 := by sorry

lemma Swap.mintedSupply (sw: Swap c s) (m: MintedTok):
  sw.apply.mintsupply m = s.mintsupply m
  := by
  simp [State.mintsupply, apply, MintedWalls.subb, MintedWalls.addb]

theorem Swap.amm_still_exists
{c: Config} {s: State} (sw: Swap c s)
{t0 t1: AtomicTok}
(h1: s.amms.f t0 t1 ≠ 0)
: sw.apply.amms.f t0 t1 ≠ 0
:= by sorry

theorem Swap.amm_fp_diff (sw: Swap c s)
(t0 t1: AtomicTok)
(exi: s.amms.f t0 t1 ≠ 0)
(hdif: (t0 ≠ sw.t0 ∨ t1 ≠ sw.t1) ∧ (t0 ≠ sw.t1 ∨ t1 ≠ sw.t0))
: sw.apply.amms.fp (sw.amm_still_exists exi)
= 
s.amms.fp exi := by sorry

theorem Swap.minted_still_supp
{c: Config} {s: State} (sw: Swap c s)
{m: MintedTok}
(h1: 0 < s.supply m)
: 0 < sw.apply.supply m
:= by sorry

theorem Swap.acc_t0_after_swap (sw: Swap c s)
: sw.apply.atoms sw.a sw.t0 
  = 
  (s.atoms sw.a sw.t0) - sw.v0
:= by sorry

theorem Swap.acc_t1_after_swap (sw: Swap c s)
: sw.apply.atoms sw.a sw.t1 
  = 
  (s.atoms sw.a sw.t1) + (sw.v0*(c.sx sw.v0 (s.amms.fp sw.exi)))
:= by sorry