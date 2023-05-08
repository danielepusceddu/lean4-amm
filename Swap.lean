import «Tokens»
import «AMMSet»
import «State»


noncomputable def Wallet.swap (w: Wallet) (amm: AMM)
  (t0: AtomicOf amm) (v0: ℝ+) (sx: @AMM.SwapRate amm)
  (_: w t0.t ≤ v0): Wallet :=
  (w.update t0.t ((w t0.t) - v0.toNNReal)).update t0.other.t ((w t0.other.t) + v0*(sx t0 v0))

noncomputable def State.swap
  (s: State) {m: MintedOf s.amms} (t0: AtomicOfM m)
  (a: Account) (sx: AMM.SwapRate) (v0: ℝ+)
  (_: s.accs a t0.t ≤ v0) -- UNUSED 'ENOUGH' HYPOTHESIS
  (nodrain: v0*(sx t0.ofAMM v0) < m.amm.r1 t0.ofAMM)
  : State := ⟨
    s.accs.update a ((s.accs a).update t0.t (((s.accs a) t0.t) - v0.toNNReal)),
    s.amms.update (m.amm.swap t0.ofAMM sx v0 nodrain)
  ⟩