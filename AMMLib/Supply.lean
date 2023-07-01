import HelpersLib.Finsupp2
import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.State
open BigOperators

noncomputable def 𝕊ₐ.supply (amms: 𝕊ₐ) (t: 𝕋₀): NNReal := (amms.f t).sum λ _ x => x.fst

noncomputable def Γ.atomsupply 
(s: Γ) (t: 𝕋₀): NNReal :=
  (s.atoms.supply t) + (s.amms.supply t)

noncomputable def Γ.mintsupply
(s: Γ) (t0 t1: 𝕋₀): NNReal :=
  s.mints.supply t0 t1

