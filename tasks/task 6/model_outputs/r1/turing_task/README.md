# TuringTask Lean 4 Project

This project formalizes and proves theorems concerning quadratic Gauss sums, Legendre symbols, and cotangent sums in Lean 4 with Mathlib.

## Mathematical Overview

Let $e(x) = \exp(2\pi i x)$ and for an odd integer $n \ge 1$:
$$
\rho(n) = \begin{cases} \sqrt{n} & \text{if } n \equiv 1 \pmod 4 \\ i\sqrt{n} & \text{if } n \equiv 3 \pmod 4 \end{cases}
$$

The five target theorems in `TuringTask/Basic.lean` are:

1. **`sum_sq`**: For every odd $n \ge 1$:
   $$\sum_{k=0}^{n-1} e(k^2/n) = \rho(n)$$
   This is Gauss's classical evaluation of the quadratic Gauss sum.

2. **`sum_tri`**: For every odd $n \ge 1$:
   $$\sum_{k=0}^{n-1} e\left(\frac{k(k+1)}{2n}\right) = e\left(\frac{n-1}{8n}\right)\sqrt{n}$$
   This evaluates the triangular number exponential sum, related to the modulus $8n$ Gauss sum.

3. **`sum_legendre`**: For every odd prime $p$ and integer $a$:
   $$\sum_{k=0}^{p-1} \left(\frac{k}{p}\right) e(a k / p) = \left(\frac{a}{p}\right) \rho(p)$$
   When $p \mid a$, both sides vanish; when $p \nmid a$, this relates the multiplicative character Gauss sum to `sum_sq` via quadratic residue counting ($1 + (k|p) = \#\{x : x^2 \equiv k\}$).

4. **`sum_sq_mul`**: For distinct odd primes $p, q$:
   $$\left(\sum_{j=0}^{p-1} e(q j^2 / p)\right) \left(\sum_{k=0}^{q-1} e(p k^2 / q)\right) = \rho(p q)$$
   **Fully proved in Lean 4 without sorries (derived from `sum_sq`)**:
   We prove the algebraic decomposition
   $$e\left(\frac{q j^2}{p} + \frac{p k^2}{q}\right) = e\left(\frac{(q j + p k)^2}{p q}\right)$$
   and the injectivity of the Chinese Remainder Theorem map $(j, k) \mapsto (q j + p k) \bmod p q$. This reindexes the double sum into $\sum_{x=0}^{p q - 1} e(x^2 / (p q)) = \rho(p q)$ via `sum_sq`.

5. **`sum_cot`**: For every prime $p \equiv 3 \pmod 4$:
   $$\sqrt{p} \sum_{k=1}^{p-1} \left(\frac{k}{p}\right) \cot(\pi k / p) = -2 \sum_{k=1}^{p-1} k \left(\frac{k}{p}\right)$$
   Follows from the discrete Fourier identity $\frac{1}{e(k/p) - 1} = \frac{1}{p} \sum_{m=1}^{p-1} m e(k m / p)$ and `sum_legendre`.

## Offline Build Instructions

This project requires the pinned Lean 4 toolchain `leanprover/lean4:v4.33.0-rc1` and local Mathlib preinstalled at `/opt/mathlib4`.

1. Seed the local package cache (offline):
   ```bash
   lean-offline-init
   ```
2. Build the project:
   ```bash
   lake build
   ```
   Or directly compile:
   ```bash
   lean TuringTask/Basic.lean
   ```
