-- | A simple FFT module based on work by David P.H. Jørgensen and
-- Kasper Abildtrup Hansen.  Uses a Stockham radix-2 algorithm.

open import "fft"
import "../complex/complex"

-- | Given a module describing real numbers, produce a module for
-- performing FFTs using Stockham's algorithm.  Requires that the
-- input is a power of two; otherwise an error is raised.
module mk_fft (R: real): {
  include fft_1d with real = R.t
  include fft_2d with real = R.t
} = {
  module complex = mk_complex R
  type real = R.t
  type complex = complex.complex

  def radix = 2i64

  def flat_index_2d [n] 'a (as: [n]a) (offset: i64) (n1: i64) (s1: i64) (n2: i64) (s2: i64) : [n1][n2]a =
    intrinsics.flat_index_2d(as, offset, n1, s1, n2, s2) :> [n1][n2]a

  def flat_update_2d [n][k][l] 'a (offset: i64) (s1: i64) (s2: i64) (asss: [k][l]a) (as: *[n]a) : *[n]a =
    intrinsics.flat_update_2d(as, offset, s1, s2, asss)

  def fft_iteration [n] (forward: R.t) (ns: i64) (data: [n]complex) (j: i64)
                  : (complex, complex) =
    let angle = R.(f64 (-2.0) * forward * pi) R.* R.i64 (j % ns) R./ R.i64 (ns * radix)
    let (v0, v1) = (data[j],
                    data[j + n / radix] complex.* (complex.mk (R.cos angle) (R.sin angle)))

    in complex.((v0 + v1, v0 - v1))

  def fft' [n] (forward: R.t) (bits: i64) (input: [n]complex) : [n]complex =
    let ix = iota (n / radix)
    let res =
      loop input = copy input for i0 < bits do
        let i = radix ** i0
        let i' = radix ** (i0 + 1)
        let (v0s, v1s) = unzip <| map (fft_iteration forward i input) ix
        let v0s = unflatten ((radix ** bits) / i') i v0s
        let v1s = unflatten ((radix ** bits) / i') i v1s
        let res = flat_update_2d i i' 1 v1s
                  (flat_update_2d 0 i' 1 v0s input)
        in res
    in res

  def log2 (n: i64) : i64 =
    let r = 0
    let (r, _) = loop (r,n) while 1 < n do
      let n = n / 2
      let r = r + 1
      in (r,n)
    in r

  def is_power_of_2 (x: i64) = (x & (x - 1)) == 0

  def generic_fft [n] (forward: bool) (data: [n](R.t, R.t)): [n](R.t, R.t) =
    let bits = assert (is_power_of_2 n) (log2 n)
    let forward' = if forward then R.i64 1 else R.i64 (-1)
    in fft' forward' bits data

  def fft [n] (data: [n](R.t, R.t)): [n](R.t, R.t) =
    generic_fft true data

  def ifft [n] (data: [n](R.t, R.t)): [n](R.t, R.t) =
    let nc = complex.mk_re <| R.i64 n
    in map (complex./nc) <| generic_fft false data

  def fft_re [n] (data: [n]R.t): [n](R.t, R.t) =
    fft (map complex.mk_re data)

  def ifft_re [n] (data: [n]R.t): [n](R.t, R.t) =
    ifft (map complex.mk_re data)

  def generic_fft2 [n][m] (forward: bool) (data: [n][m](R.t, R.t)): [n][m](R.t, R.t) =
    let n_bits = assert (is_power_of_2 n) (log2 n)
    let m_bits = assert (is_power_of_2 m) (log2 m)
    let forward' = if forward then R.i64 1 else R.i64 (-1)
    in map (fft' forward' m_bits) data
       |> transpose
       |> map (fft' forward' n_bits)
       |> transpose

  def fft2 [n][m] (data: [n][m](R.t, R.t)): [n][m](R.t, R.t) =
    generic_fft2 true data

  def ifft2 [n][m] (data: [n][m](R.t, R.t)): [n][m](R.t, R.t) =
    let nc = complex.mk_re <| R.i64 <| n * m
    in map (map (complex./ nc)) (generic_fft2 false data)

  def fft2_re [n][m] (data: [n][m]R.t): [n][m](R.t, R.t) =
    fft2 (map (map complex.mk_re) data)

  def ifft2_re [n][m] (data: [n][m]R.t): [n][m](R.t, R.t) =
    ifft2 (map (map complex.mk_re) data)
}
