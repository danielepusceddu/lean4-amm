import HelpersLib.Finsupp2
import AMMLib.State.Tokens
import AMMLib.State.AMMSet
import AMMLib.State.State
open BigOperators
open NNReal

noncomputable def Sₐ.supply (amms: Sₐ) (t: T): ℝ≥0 := (amms.f t).sum λ _ x => x

noncomputable def Γ.atomsupply
(s: Γ) (t: T): ℝ≥0 :=
  (s.atoms.supply t) + (s.amms.supply t)

noncomputable def Γ.mintsupply
(s: Γ) (t0 t1: T): ℝ≥0 :=
  s.mints.supply t0 t1
