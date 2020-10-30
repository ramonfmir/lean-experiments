import data.mv_polynomial
import data.real.basic

section mv_taylor_models

structure taylor_model
(n : ℕ)
(f : mv_polynomial (fin n) ℝ)
(I : fin n → ℝ × ℝ)

end mv_taylor_models
