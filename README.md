# NRS³ · Tritoro — el campo de incertidumbre en T³

**Los tres ejes cerrados.** `T³ = x × y × z`, cada eje cerrado con tres posiciones: finito y sin
borde. Cada eje lleva el par `(T°, P₃)` del eje cerrado. La teoría del campo de incertidumbre
𝒰 y su nivel de campo se mudan aquí, fuera de la caja de cuatro ejes de `nrs3-hopf`.

Lean 4 sobre [`nrs3-hopf`](../nrs3-hopf) (lemas del eje cerrado: `ClosedThree`,
`ClosedAxisEntangled`, `StackedFibers`, `ClosedThreeIdeal`, `RobertsonEquality*`),
[`nrs3-dark`](../nrs3-dark) y [`nrs3-uncertainty-cone`](https://github.com/naype888-cloud/nrs3-uncertainty-cone).
Dependencias por git, fijadas a un commit: [`nrs3-hopf`](https://github.com/naype888-cloud/nrs3-hopf), [`nrs3-dark`](https://github.com/naype888-cloud/nrs3-dark), [`nrs3-mandelstam-tamm-cramer-rao`](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao) y [`nrs3-de-sitter`](https://github.com/naype888-cloud/nrs3-de-sitter). Páginas: [de Sitter en T³](https://naype888-cloud.github.io/nrs3-de-sitter/t3.html), [SL(2, ℂ) en T³](https://naype888-cloud.github.io/nrs3-uncertainty-cone/lorentz-t3.html), [NRS³-Minkowski en T³](https://naype888-cloud.github.io/nrs3-uncertainty-cone/index-t3.html), [Dark en T³](https://naype888-cloud.github.io/nrs3-dark/t3.html).

## Three topologies: R³, T³ and the fibred box

`R³`: the open cube, every axis open. `T³`: every axis closed. Fibred box: `x`, `y`, `z` open and
the fiber `w` closed with three positions (`nrs3-hopf`).

| | R³ | T³ | Fibred box |
|---|---|---|---|
| uncertainty relation / covariance determinant | Physlib #1723 (NRS), #1725 (NRS³) | `Torus.robertson_det_torus`, `TorusStrict.robertson_det_torus_lt` | `BoxStrict.robertson_det_box_lt`, `NRSCell16` |
| light share / dark share | `DarkShare.lightShare_maxCurrentState`; limit ≈ 0.775 | `TorusDark.lightShare_maxState` (4/5, 1/5); limit ½ (`RingSzego`) | `FiberDark.darkShare_pos_of_band`, `lightShare_fiberMaxState` (4/5, 1/5) |
| boundary entropy / area law | one wall, `dy·dz`: `OpenCubeBoundary.bekenstein_bound` | two walls, `2·dy·dz`: `TorusBekenstein.bekenstein_bound` | `dy·dz·3` across `x`, `2·dx·dy·dz` across `w`: `FiberBoundary.entropy_le_x`, `entropy_le_w` |
| saturation / uniform field | `OpenCubeBoundary.saturated_iff_uniform`, `openProb_uniform` | `TorusSaturation.saturated_iff_uniform`, `TorusDarkFoam.meanField_uniform` | `FiberBoundary.saturated_iff_uniform_w`, `openProb_uniform_w` |
| Bakry–Émery curvature / Ricci lower bound | flat, `CD(0, 2)`: `BakryEmery.path_CD02` | flat: `TorusBochner.not_curvature_pos` | `K = 4` (16-cell): `BochnerCurvature.cell16_curvature` |
| Lorentz cone / admissible cone | `UncertaintyCone.mem_futureCone` | `TorusCone.axisVector_mem_futureCone` | `BoxCone.axisVector_mem_futureCone` |
| Dirac operator / doubler modes | `D_m² = T² + m²`, every size: `OpenDirac.dirac_sq` | even sizes, eight doublers: `TorusDirac3.dirac3_sq`, `dirac3_wave` | the fiber is the mass, `1` and `1/2`: `FiberDirac.dirac_sq`, `fiberMass_sq` |
| Einstein / Unruh flow | `η = 1/(4ℓ_P²)`, `R_kk = 8πℓ_P² T_kk`: `CutEinstein.clausius_openCube` | `CutEinstein.clausius_torus` | `CutEinstein.clausius_fiber` |

On every cut `η = 1/(4ℓ_P²)` (`ClausiusInput`, `FiberBoundary.eta_w`), so with the Unruh
temperature (`Rindler.unruhTemperature_mul_period`) the Clausius relation on every light sheet is
`R_kk = 8πℓ_P² T_kk` (`LightSheet.eight_pi`), and on every light sheet through every point it gives
`Ric − ½R g + Λ g = 8πℓ_P² T` (`CutEinstein.einstein_cut`, from `Einstein.einstein_equation`).

## Resultados

| Enunciado | Lean |
|---|---|
| Robertson 1934 en el toro, todo estado | `Torus.robertson_det_torus` |
| NRS³ en cada eje: tensión > 1 ⇒ defecto > 0, todo estado, entrelazado o no | `Torus.gramDefect_pos` |
| en el estado de corriente máxima `det Σ = (5/4)^k \|det Ω\|` | `Torus.det_covMatrix_maxState` |
| `T³`: `125/64`; `T⁴`: `625/256`; estricto desde `k = 1` | `Torus.three_torus`, `Torus.four_torus`, `Torus.robertson_det_maxState_strict` |
| escalera: cubo abierto `1`, caja `5/4`, `T³` `125/64`, `T⁴` `625/256` | `Torus.ladder` |
| los ejes distintos del toro conmutan | `TorusCommute.liftAlong_split_comm`, `TorusCommute.torusPairs_comm` |
| `[[T°, P₃], w₀T° + w₁P₃] ≠ 0` para `w ≠ 0` | `TorusStrict.lie_lie_ne_zero` |
| **det\|NRS³\| estricto en `T³` para todo estado con los tres ejes en su banda** | `TorusStrict.robertson_det_torus_lt` |
| todo eje de todo estado cae en el cono futuro cerrado | `TorusCone.axisVector_mem_futureCone` |
| el intervalo de un eje es su defecto de Robertson–Schrödinger | `TorusCone.interval_axisVector` |
| en la banda el eje es estrictamente temporal; tiempo propio > 0 | `TorusCone.timelike_of_band`, `TorusCone.properTime_pos_of_band` |
| luz + oscuro = 1 en cada eje, todo estado | `TorusDark.lightShare_add_darkShare` |
| en la banda cada eje guarda una parte oscura > 0, todo estado | `TorusDark.darkShare_pos_of_band` |
| en `c` cada eje resuelve `4/5` y guarda `1/5` oscuro (el cubo abierto de 3 guarda `0`) | `TorusDark.lightShare_maxState`, `TorusDark.darkShare_maxState` |
| **ley de área del toro**: el corte `{x ≤ c}` tiene dos caras, el plano y la costura, con `dy·dz` pasos cada una; `S = 2·dy·dz·log 2`, sin depender de la profundidad `dx` ni del plano | `TorusArea.card_planeSteps`, `card_seamSteps`, `card_crossSteps`, `cutEntropy_eq`, `cutEntropy_eq_of_depth` |
| Bekenstein–Hawking: con área `a²` por paso, `S = a²A/(4ℓ_P²)` ⟺ `a² = 4ℓ_P² log 2`, el mismo bit que en el cubo abierto | `TorusArea.bekensteinHawking_iff` |
| defecto del corte `Ω = 2·dy·dz·δ(dx)`, mitad por cara; desde `4` posiciones `S = (log 2/δ) Ω`; las tres caras cargan `Ω_xΩ_yΩ_z = 8V²𝒱` y el cuanto del interior se lee en el borde, `𝒱 = (log 2)³ Ω_xΩ_yΩ_z/(S_xS_yS_z)` | `TorusArea.cutDefect_eq`, `cutEntropy_eq_mul_cutDefect`, `prod_cutDefect`, `volQuantum_eq_boundary` |
| **bits del borde, para cualquier corte**: un borde de `n` pasos guarda a lo más `n log 2`; solo la uniforme lo llena; en ella cada paso está abierto la mitad del tiempo y fluctúa `1/4` (T³, el cubo abierto y la caja con fibra usan lo mismo) | `BoundaryBits.entropy_le`, `saturated_iff_uniform`, `openProb_uniform`, `bitVariance_uniform` |
| **R³, el cubo abierto**: sin costura, el corte `{x ≤ c}` es solo el plano, `dy·dz` pasos; el borde de T³ es ese más la costura; Bekenstein `H ≤ dy·dz·log 2 = A/(4ℓ_P²)`, lleno = uniforme, y la misma espuma | `OpenCubeBoundary.T3_ne_zero_iff`, `openCrossSteps_eq`, `crossSteps_eq_union`, `bekenstein_bound`, `saturated_iff_uniform`, `openProb_uniform`, `bitVariance_uniform` |
| **R³, Dirac en la caja abierta**: un paso de un eje abierto siempre cambia el signo, `σT = −Tσ` para todo tamaño; Kogut–Susskind `D_m² = T_x² + T_y² + T_z² + m²` sin paridad (en T³ hacen falta lados pares); el álgebra se hace una vez en cualquier anillo | `OpenDirac.stagger_mul_Td`, `dirac_sq`, `sq_add_of_anticomm`, `dirac_sq_of_relations` |
| **entrada de Clausius**: con un bit y área `a²` por paso, `η = S/A = log 2/a²` en todo corte, de T³ y del cubo abierto, de cualquier tamaño; con el bit de área, `η = 1/(4ℓ_P²)`, el valor que da `8πG` en el paso de Clausius (G4) | `ClausiusInput.entropyPerArea_eq`, `torus_eta`, `openCube_eta`, `eta_universal` |
| **Fibra, luz / oscuro**: en la fibra cerrada de la caja (x, y, z abiertos, w anillo de 3) luz + oscuro = 1 para todo estado; en la banda la fibra guarda parte oscura > 0 aunque esté entrelazada con x, y, z; en el `c` de la fibra resuelve `4/5` y guarda `1/5`, como cada eje de T³ | `FiberDark.lightShare_add_darkShare`, `darkShare_pos_of_band`, `lightShare_fiberMaxState`, `darkShare_fiberMaxState` |
| **Fibra, bits y espuma**: cortar a través de x es un muro (`dy·dz·3` pasos, como R³); cortar a través de la fibra son dos muros (`2·dx·dy·dz`, como T³); Bekenstein, lleno = uniforme, la misma espuma y el mismo `η = 1/(4ℓ_P²)` | `FiberBoundary.card_xSteps`, `card_wSteps`, `entropy_le_x`, `entropy_le_w`, `saturated_iff_uniform_w`, `openProb_uniform_w`, `bitVariance_uniform_w`, `eta_x`, `eta_w` |
| **Fibra, Dirac: la fibra es la masa** (Kaluza–Klein): el anillo de 3 es impar y no admite signo alternado, así que entra como masa, `D = T_x + σ_x T_y + σ_xσ_y T_z + σ_xσ_yσ_z T°` y `D² = T_x² + T_y² + T_z² + T°²`; los modos de la fibra dan las masas `1` (uniforme) y `1/2` (los que giran) | `FiberDirac.dirac_sq`, `dirac_sq_fiber_of_relations`, `Tc_uniform`, `Tc_rotating`, `fiberMass_sq` |
| **cota de Bekenstein en T³**: toda distribución de los bits del borde tiene `H ≤ S = 2·dy·dz·log 2`; con el bit de área, `H ≤ A/(4ℓ_P²)`; la uniforme la alcanza | `TorusBekenstein.entropy_le_cutEntropy`, `entropy_le`, `bekenstein_bound`, `entropy_uniform`, `exists_saturating` |
| **saturada = perfectamente distribuida**: `H = S` ⟺ la distribución del corte es la uniforme (igualdad de Jensen para `−x log x` estrictamente cóncava); la región oscura del postulado es esa | `TorusSaturation.eq_uniform_of_entropy_eq`, `saturated_iff_uniform`, `HSaturationDark.eq_uniform_of_saturation` |
| **los bits del borde los carga el campo**: cada configuración `S` es el operador `F(S) = Σ_{(p,q) ∈ S} [T3c, P_x]_pq a†_p a_q` (paso abierto = el campo mueve una excitación a través del corte); con la estructura estrella `dΓ` es inyectiva, `S ↦ F(S)` también, el campo carga `2^(2·dy·dz)` configuraciones y `log #F = S` | `TorusBoundaryField.secondQuant_injective`, `configField_eq_sum`, `configField_injective`, `card_fieldConfigs`, `log_card_fieldConfigs` |
| **el campo oscuro es espuma**: en la uniforme (y en toda distribución saturada) cada paso del borde está abierto con probabilidad `1/2`, sin gradiente; el corchete medio es la mitad del corchete completo en cada paso, `Σ_S d(S) F(S) = ½ F(todo abierto)`; cada paso fluctúa lo máximo que puede un bit, `p(1−p) = 1/4` | `TorusDarkFoam.openProb_uniform`, `meanBracket_uniform`, `meanField_uniform`, `bitVariance_le`, `bitVariance_uniform`, `openProb_of_saturated`, `meanBracket_of_saturated`, `bitVariance_of_saturated` |
| **Bochner en T³: el toro es plano**: con el transporte de seis vecinos, `Γ₂(f)` es una suma de cuadrados de segundas diferencias (por eje y mixtas entre pares de ejes), así que `Γ₂ ≥ 0`, curvatura `≥ 0` para todo tamaño; con `5` posiciones en un eje la cota es justa (`Γ = 1`, `Γ₂ = 0`) y ningún `K > 0` vale; `Γ = ½[f,[f,A]]1` lee la curvatura del corchete de NRS (el 16-cell, en cambio, tiene `K = 4`) | `TorusBochner.gam2_eq`, `torus_curvature`, `torus_sharp`, `not_curvature_pos`; `BochnerCurvature.gamma_eq_lie` |
| una región saturada (`H = S`) está llena: ninguna distribución del corte guarda más; **postulado de Nava (puente declarado)**: saturar un cuanto lo vuelve oscuro, parte oscura `1` y luz `0`; satisfacible; la uniforme y toda región que alcanza `A/(4ℓ_P²)` son oscuras | `TorusSaturation.isMax_of_saturated`, `HSaturationDark`, `hSaturationDark_satisfiable`, `HSaturationDark.darkShare_uniform`, `lightShare_eq_zero`, `darkShare_of_area` |

| sector de **dos excitaciones**: `dΓ M (Σ Ψ a†a† Ω) = Σ (D M Ψ) a†a† Ω`, con `D M = M ⊗ 1 + 1 ⊗ M` | `TorusSectors.secondQuant_twoExcitation` |
| `D ⁅M, N⁆ = ⁅D M, D N⁆` | `TorusSectors.twoBody_lie` |
| la forma `β` en dos excitaciones es `Ψ̄ · (Φ + Φᵀ)`; en simétricos, `2 Ψ̄ · Φ` | `TorusSectors.form_twoExcitation`, `form_twoExcitation_symm` |
| el campo de incertidumbre de dos excitaciones es el de `D M, D N` sobre `√2 Ψ` | `TorusSectors.uncertainty_twoExcitation` |
| el corchete del campo en dos excitaciones lee `2 Ψ̄ · D[T3c, P_x] Ψ` | `TorusSectorCut.form_bracket_two` |
| los pasos del corte de dos excitaciones: un paso de frontera de una, la otra quieta | `TorusSectorCut.bracketTwoSteps_eq` |
| son `2 · (dx·dy·dz) · (2·dy·dz)` | `TorusSectorCut.card_bracketTwoSteps` |
| patrones en dos excitaciones = conjuntos cerrados e invariantes por intercambio; a lo más `2^(N·2dydz)`, estrictamente menos | `TorusSectorPatterns.mem_patterns_iff`, `card_patterns_le`, `card_patterns_lt` |
| sector de `n` excitaciones: `dΓ M` actúa como `D_n M` (una posición a la vez) | `TorusFock.secondQuant_nExcitation` |
| `D_n ⁅M, N⁆ = ⁅D_n M, D_n N⁆` | `TorusFock.nBody_lie`, `nBodyMat_lie` |
| en simétricos `β = n! Ψ̄ · Φ` | `TorusFock.form_nExcitation_symm` |
| el campo de incertidumbre de `n` excitaciones es el de `D_n M, D_n N` sobre `√(n!) Ψ` | `TorusFock.uncertainty_nExcitation` |
| el corte de `n` excitaciones: `n·(2dydz)·(dxdydz)^(n-1)` pasos | `TorusFockCut.card_bracketNSteps` |
| eje cerrado en `ℂ^d`: todo estado unitario con `\|t\| ≥ 1` concentra su peso en la costura, `Var T° → 1/2`, `Var P → 1`, `Cov → 0` | `RingSzego.seam_bounds`, `tendsto_variance_transport`, `tendsto_variance_PdOp`, `tendsto_covariance` |
| dipolo `ℓ = 1` ↔ tres ejes; modo puro de eje `m`: `T = cos`, `P = sin`, `T²+P² = 1`; `T3c` lo manda a `(T+2)` veces sí mismo | `TorusDipole.axis_bijective`, `transport_sq_add_momentum_sq`, `lam3_axisMode`, `T3c_axisMode` |
| **límite de Szegő del eje cerrado**: luz y oscuro → `1/2`, ángulo → `45°` | `RingSzego.tendsto_lightShare`, `tendsto_darkShare`, `tendsto_angle` |
| `det Σ / \|det Ω\|` del eje → `2` | `RingSzego.tendsto_det_ratio` |
| todo tamaño tiene su estado `c`; en `c` el ángulo → `45°` y la razón → `2` | `RingSzego.exists_cState`, `tendsto_angle_cState`, `tendsto_det_ratio_cState` |
| eje del universo `ZMod L`, `L = M d`: dentro de un cubo `i[T°, X] = s K`; si todos los enlaces menos uno avanzan `s`, el último avanza `−(L − 1) s` (el salto `−2` de la costura de `P_d`); ninguna coordenada avanza el mismo paso no nulo en todo el eje | `TorusUniverse.commutator_apply_of_steps`, `closing_step`, `step_eq_zero` |
| nada avanza más de una posición por paso: `\|⟨K⟩\| ≤ 1`; `⟨T°⟩² + Var T° + ⟨K⟩² + Var K = 1`, y `Var T° > 0` da `\|⟨K⟩\| < 1`; el modo de fase `i^j` va a `−1` con `T° i^j = 0` (`4 ∣ L`) | `TorusUniverse.abs_velocity_le`, `statistics_sum`, `abs_velocity_lt_one`, `current_phaseMode`, `transport_phaseMode` |
| Robertson–Schrödinger en el eje del universo: el excedente es la brecha de Cauchy–Schwarz, `≥ 0`, y se anula exactamente con `T̃Ψ = κ X̃Ψ` | `TorusUniverse.surplus_eq`, `surplus_nonneg`, `exists_parallel_of_surplus_eq_zero` |
| las dos ondas más rápidas `e_{±i}` (`4 ∣ L`): `S e_u = u e_u`, `T° e_u = 0`, ortogonales, `X` las acopla con `−1/2`; `S − u` acotado por debajo fuera de `e_u`; `‖(S ∓ i)Ψ‖² = 2 ± 2⟨K⟩` | `TorusUniverse.shift_wave`, `transport_wave`, `inner_wave_chart`, `exists_gap`, `norm_sq_shift_sub_I` |
| los estados que saturan con `Var T° > 0` quedan lejos de las ondas más rápidas | `TorusUniverse.exists_transport_gap`, `isolation` |
| **banda del eje del universo**: saturar con `Var T° > 0` da `\|⟨K⟩\| ≤ 1 − ε`; `v*(L) < 1`, la banda `Ϙ(L) = (v*(L), 1)` nunca es vacía y en ella el excedente es estrictamente positivo | `TorusUniverse.exists_velocity_le`, `threshold_lt_one`, `band_nonempty`, `surplus_pos_of_mem_band` |
| dobladores del eje (`L` par): el signo alternado `Σ` anticonmuta con `T°` y `K` e intercambia `e_u ↔ e_{−u}`; es la `β` de Dirac, y `D_m = T° + m Σ` cumple `D_m² = T°² + m²`; con `m ≠ 0` ningún estado estacionario llega al cono | `TorusUniverse.transport_stagger`, `current_stagger`, `stagger_wave`, `dirac_sq`, `abs_velocity_lt_one_of_dirac` |
| límite de velocidad de un estado de Dirac con masa: `T°² + K² = 1` y `\|⟨K⟩\| ≤ √(1 + m²) − \|m\| < 1` (en `m = 1/2`, `1/φ`) | `TorusUniverse.transport_sq_add_current_sq`, `abs_velocity_le_of_dirac` |
| raíz de Dirac en `T³` (lados pares, signos de Kogut–Susskind): `D_m² = T_x² + T_y² + T_z² + m²`; los ocho dobladores `(±π/2)³` (`4` divide cada lado) cumplen `D_m e_{uvw} = m e_{−u,−v,−w}`, ceros de `D_0` | `TorusDirac3.dirac3_sq`, `dirac3_wave` |

### La prueba del estricto, en una línea por paso

1. En la igualdad cada eje tiene defecto, así que las relaciones (dimensión ≥ 3) cruzan cada eje
   en las dos direcciones.
2. Una relación `r` nula en `x`, una `t` nula en `y`, una `s` independiente de `r` en `z`:
   `[[r, s], t]` vive solo en `z` y no es cero.
3. Las partes en `z` forman un subespacio sin traza estable bajo `T°`, `P₃`: contiene todas las
   `E_ij`.
4. `E₀₀ − E₁₁` y `E₁₁ − E₂₂` en `z` anulan el estado y no tienen núcleo común: no queda estado.

En la caja de cuatro ejes los ejes abiertos necesitaban pasos iguales (`EqualSteps`); en el toro
todos los ejes son cerrados y el doble corchete basta.

## Pendiente (orden del porte)

Hecho: ley de área, Mandelstam–Tamm, nivel de campo `n = 1`, costuras LQG / de Sitter, patrones de corte,
sector `n = 2` y sus pasos de corte. Hecho también: caracterización de los patrones de `n = 2` y sectores `n` generales con su corte. Abierto: conteo exacto de patrones de `n = 2` y patrones de `n ≥ 3`.

Nota sobre los patrones en `n = 2`: un estado simétrico abre un paso de una excitación junto con su
imagen intercambiada, y si abre `(a,r)→(b,r)` por separado en dos pasos de la otra excitación también
lo abre sin quererlo. El conjunto de patrones no es todo el conjunto potencia como en `n = 1`; contarlo
es trabajo abierto, no está en Lean.

## Verificación

`lake build` y `lake env lean Verification/Axioms.lean`: solo `propext`, `Classical.choice`,
`Quot.sound`.

**[▶ The baryon window on the ring](https://naype888-cloud.github.io/nrs3-tritoro/baryon.html)** · [Holography: open cube and T³](https://naype888-cloud.github.io/BACQM-NRS3/didactic/holography.html) — at the ring limit `c = √2` the window is positive (`window_sqrt_two_pos`): the limit does not saturate.

**[▶ Bits on the boundary](https://naype888-cloud.github.io/BACQM-NRS3/didactic/bekenstein.html)** · **[▶ The dark foam](https://naype888-cloud.github.io/BACQM-NRS3/didactic/foam.html)** — a region of T³ holds at most one bit per square of its walls, whatever its depth (`bekenstein_bound`); only the perfectly mixed state fills it (`saturated_iff_uniform`), and Nava's postulate makes it dark; that state is a foam, flat on average and flipping the most at every square (`openProb_uniform`, `bitVariance_uniform`); and by Bochner the torus is flat (`torus_curvature`, `not_curvature_pos`).
