import «AMMSet»
import «State»

namespace Deposit0

structure Valid (s: State) where
  t0: AtomicTok
  t1: AtomicTok
  r0: ℝ+
  r1: ℝ+
  a: Account
  hdif: t0 ≠ t1
  hnin: ⟨{t0,t1}, by aesop⟩ ∉ s.amms.map.supp
  hen0: (s.accs a) t0 ≤ r0
  hen1: (s.accs a) t1 ≤ r1 

def amm {s: State} (v: Valid s): AMM :=
  ⟨
  (PFun.empty.update v.t0 v.r0).update v.t1 v.r1, by 
  simp [PFun.update, PFun.empty];
  exact Finset.card_doubleton v.hdif.symm
  ⟩

noncomputable def wallet {s: State} (v: Valid s): Wallet :=
  ((s.accs v.a).update v.t0 (((s.accs v.a) v.t0) - v.r0)).update v.t1 (((s.accs v.a) v.t1) - v.r1)

noncomputable def apply {s: State} (v: Valid s): State :=
  ⟨
  s.accs.update v.a (wallet v),
  s.amms.update (amm v)
  ⟩