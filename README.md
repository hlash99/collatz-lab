# Collatz lab

An interactive sandbox for the 3n+1 problem, live at **https://hlash99.github.io/collatz-lab/**.

Everything runs client-side with BigInt — no server, no build step, one `index.html`.

## Panels

- **Orbit explorer** — Syracuse orbits of arbitrary-size integers under 3n+1 / 5n+1 / 7n+1, with measured vs predicted drift.
- **Carry microscope** — the exact theorem `v₂(3n+1) = length of the trailing match between n and the 2-adic −1/3 (…0101₂)`, watchable step by step.
- **Pattern programmer** — solves for the unique residue class mod 2^(Σkᵢ+1) realizing any prescribed division pattern (Terras 1976 coding, computed by 2-adic lifting).
- **Thermalization** — precomputed zlib-complexity series along orbits: structured seeds gain entropy until incompressible, then ride the average drift down.
- **Seed-horizon lab** — new measurement: past the provable prefix of a 2^k−1 seed, the self-generated division stream is statistically geometric(1/2) (offline aggregate: 38,299 steps, mean v₂ 2.007, χ² 16.5/10 df, lag-1 autocorrelation 0.007).
- **Insights** — what this proves about why the conjecture is hard, including the 5n+1 falsification razor for proposed proof mechanisms.

Offline verifications were run in Python (exhaustive theorem check for all odd n < 2×10⁶, horizon statistics, compression series) and are reproduced live in the browser where feasible.

Built with Claude Code · July 2026
