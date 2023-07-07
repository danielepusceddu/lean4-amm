import HelpersLib.Finsupp2
import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.State
open BigOperators

noncomputable def 𝕊ₐ.supply (amms: 𝕊ₐ) (t: 𝕋): NNReal := (amms.f t).sum λ _ x => x

noncomputable def Γ.atomsupply 
(s: Γ) (t: 𝕋): NNReal :=
  (s.atoms.supply t) + (s.amms.supply t)

noncomputable def Γ.mintsupply
(s: Γ) (t0 t1: 𝕋): NNReal :=
  s.mints.supply t0 t1

