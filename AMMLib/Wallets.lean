import Mathlib.Data.Finsupp.Basic
import AMMLib.Tokens

abbrev 𝕎₀ := 𝕋₀ →₀ NNReal
abbrev 𝕎₁ := 𝕋₁ →₀ NNReal
abbrev 𝕊₀  := 𝔸 →₀ 𝕎₀
abbrev 𝕊₁  := 𝔸 →₀ 𝕎₁

noncomputable def 𝕊₀.addb (as: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (v: NNReal)
  : 𝕊₀ := as.up a t ((as a t) + v)

noncomputable def 𝕊₀.subb (as: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (v: NNReal)
  : 𝕊₀ := as.up a t ((as a t) - v)

noncomputable def 𝕊₁.addb (as: 𝕊₁) (a: 𝔸) (t: 𝕋₁) (v: NNReal)
  : 𝕊₁ := as.up a t ((as a t) + v)

noncomputable def 𝕊₁.subb (as: 𝕊₁) (a: 𝔸) (t: 𝕋₁) (v: NNReal)
  : 𝕊₁ := as.up a t ((as a t) - v)