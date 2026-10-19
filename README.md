# NRS³ · Tritoro — el campo de incertidumbre en T³

**Los tres ejes cerrados.** `T³ = x × y × z`, cada eje cerrado con tres posiciones: finito y sin
borde. Cada eje lleva el par `(T°, P₃)` del eje cerrado. La teoría del campo de incertidumbre
𝒰 y su nivel de campo se mudan aquí, fuera de la caja de cuatro ejes de `nrs3-hopf`.

Lean 4 sobre [`nrs3-hopf`](../nrs3-hopf) (lemas del eje cerrado: `ClosedThree`,
`ClosedAxisEntangled`, `StackedFibers`, `ClosedThreeIdeal`, `RobertsonEquality*`),
[`nrs3-dark`](../nrs3-dark) y [`nrs3-uncertainty-cone`](https://github.com/naype888-cloud/nrs3-uncertainty-cone).
Solo local, dependencias por ruta.

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

reparto luz/oscuro (`DarkShare`) → ley de área `S → Λ` → Mandelstam–Tamm → nivel de campo
(`FieldLevel`, sector `n = 1`) → costuras LQG / de Sitter.

## Verificación

`lake build` y `lake env lean Verification/Axioms.lean`: solo `propext`, `Classical.choice`,
`Quot.sound`.
