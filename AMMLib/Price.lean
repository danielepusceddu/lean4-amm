import AMMLib.Supply

noncomputable def Γ.𝕋₁Price_denumz
(s: Γ) (m: 𝕋₁): NNReal := s.mintsupply m

noncomputable def Γ.𝕋₁Price_num_addend1z
(s: Γ) (o: 𝕋₀ → PReal)
(m: 𝕋₁)
: NNReal := (s.amms.f m.choose m.other).fst * (o m.choose)

noncomputable def Γ.𝕋₁Price_num_addend2z
(s: Γ) (o: 𝕋₀ → PReal)
(m: 𝕋₁)
: NNReal := (s.amms.f m.choose m.other).snd * (o m.other)

noncomputable def Γ.𝕋₁Price_numz
(s: Γ) (o: 𝕋₀ → PReal)
(m: 𝕋₁)
: NNReal :=
(s.𝕋₁Price_num_addend1z o m) + (s.𝕋₁Price_num_addend2z o m)

noncomputable def Γ.𝕋₁Pricez
(s: Γ) (o: 𝕋₀ → PReal)
(m: 𝕋₁): NNReal :=
(s.𝕋₁Price_numz o m) / (s.𝕋₁Price_denumz m)