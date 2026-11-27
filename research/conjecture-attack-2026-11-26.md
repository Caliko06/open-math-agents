# Ataque a conjetura abierta — dossier de investigación

Fecha: 2026-11-26 · Agente: opencode (GLM) · Crédito: @Caliko06

## Reglas del OWNER

1. La conjetura no debe estar ya resuelta (probada/refutada) — verificada contra literatura 2024–2026.
2. Todo el trabajo se documenta en este dossier.
3. Prohibido hillclimb y caso numérico ("caso n de X" / enésima versión / cota asintótica): se exige enunciado principal — existencia, clasificación o estructura.

## Método (/default-principles)

1. Problema real: elegir la conjetura abierta correcta y atacarla con criterio; no prometer resolución a ciegas.
2. El default (lo que diría sin leer) no es la respuesta: cada apertura, cota y ataque se verifica con fuentes.
3. Prior art antes de atacar: arXiv, erdosproblems.com, repos, foros, 2024–2026 incluido.
4. Cada hipótesis apunta a fuentes y a una medición que la confirma o la tumba.
5. Evidencia etiquetada: HECHO / INFERENCIA / SIN SABER. Nada se construye sobre memoria.

## Enjambre (7 carriles, en paralelo)

| Carril | Objetivo | Estado |
|---|---|---|
| S1 scan | Censo completo del catálogo open del desk (~1939), clasificación no-numérica, top-10 atacables | corriendo |
| S2 | Agoh–Giuga: apertura, equivalencias (Giuga/Carmichael), ataque | corriendo |
| S3 | Kurepa (factorial izquierdo): apertura, cotas de verificación, ataque | corriendo |
| S4 | Fuglese dim 1: estado por dirección, parcial 2024–2026, ataque | corriendo |
| S5 | Ben Green 24/40/64/72/100: cuál es la más atacable | corriendo |
| S6 | Erdős 1053/1055/1160/1186/835/137/364/307: la más atacable | corriendo |
| S7 | Fibonacci-primes/Cramér/ABC/Kaplansky/Auslander–Reiten/anti-hydra: ranking | corriendo |

## Tabla de hipótesis (por llenar con los reportes S1–S7)

| Hipótesis (conjetura candidata) | Fuentes | Qué tomo | Cómo se mide el ataque | Plan si se confirma |
|---|---|---|---|---|
| Agoh–Giuga (HECHO: abierta; prueba elemental de 2011 retractada; sin claims 2024–26) | lefttosolve API; Integers/Springer (cota contraejemplo ≥ 19,908 dígitos); arXiv 2610.09129, 2607.18607 (estructura 2026); Wikipedia (equivalencias Giuga↔Carmichael↔primary pseudoperfect) | Núcleo abierto: ningún cuadrado-libre compuesto satisface Korselt+Giuga (R1.H3 del desk); cotas duras; condiciones necesarias nuevas | Reducciones formalizadas sin sorry; dígitos de cota verificada — no la conjetura completa | Solo contribución incremental (H2/H3, 15 pts); resolución = décadas. DESCARTADA como objetivo principal |
| Fuglese dim 1 (HECHO: abierta; dim 2 refutada por Tao–Zhang 2026, arXiv 2607.15632, sin referato) | arXiv 2607.15632; 2609.14026 (CM completa ⟹ tile⟹spectral dim 1, preprint 2026); 2610.02218 (cíclicos cuadrado-libres); 2607.26534 (inducción Somlai); 2207.11809 (Łaba–Londner T2); lefttosolve API | Hueco exacto: spectral⟹tile para espectros no estándar (= UTC); estructura de reducción cíclicos→ℤ→ℝ | Verificación computacional de Fuglede en ℤ_N no cuadrado-libre; auditoría del preprint 2609.14026 | Útil solo como auditoría/verificación computacional; conjetura completa = décadas. DESCARTADA como objetivo principal |
| Kurepa gcd (HECHO: abierta; Abramov 2022 retiró su claim en v3; verificada p < 2^40) | lefttosolve API (statement exacto, FormalConjectures/Paper/Kurepa.lean:96); arXiv 2209.12677 (retractada); Andrejić–Bostan–Tatarević (cota 2^40); arXiv 2509.06077, 2609.28805 (actividad 2025-26 sin prueba); benchmark arXiv 2610.37739 | Nada estructural que extender; equivalencias van por Bell/derangements, no permutaciones alternantes (SIN SABER esa conexión) | Prueba formal sin sorry, o contraejemplo p impar ∣ !(p−1) (descartado hasta 2^40) | Solo formalizar reducciones; demostración = décadas. DESCARTADA como objetivo principal |
| Green 40 (HECHO: abierta; frontera activa: f(2) bajó 3× en 12 meses; precedida de resolución finita por agentes, arXiv 2608.27494) | lefttosolve API; Green open-problems.pdf §5; arXiv 2511.02542, 2609.16078 (cotas f(2)≤2601/2048); 2608.27494 (ℓ₂(10,2)≤50 vía SAT+QM22) | Plantilla SAT/ILP→verificador→QM22; hueco ℓ₂(8,2)≤26, ℓ₂(9,2)≤39; ángulo estructural: forzar linealidad vía simetrías SAT | Síndromes cubiertos por k columnas en F₂ʳ y cota f(2) resultante; a meses: decidir f(2)=1 o f(r)→∞ | CANDIDATA LÍDER — con reserva: mejorar récord = hillclimb (regla 3); el objetivo legítimo es el enunciado completo f(r)→∞ o refutarlo con f(2)=1 |
| Anti-hydra set (HECHO: abierta; cero literatura experta, solo simulación a 2^38; ya formalizada en Lean en formal-conjectures) | wiki.bbchallenge.org/wiki/Antihydra; TMBR oct 2026 (verificación empírica independiente); lefttosolve API | Enunciado autocontenido a(0)=8, a(n+1)=⌊3a(n)/2⌋; superficie intacta; cualquier parcial con prueba (invariantes, deriva impar/par, equivalencia set/recurrencia) es contribución | Resultados parciales demostrados + formalización Lean; riesgo dureza Collatz/BB(6) | CANDIDATA — resolución total = décadas; contribución parcial documentable en sesión. A confirmar contra S6/S1 |
| Kaplansky u-invariante (HECHO: abierta y viva; Karpenko 2026 resolvió todo salvo u=2^r−1 y 2^r−3) | arXiv 2608.08052; sites.ualberta.ca/~karpenko | Frontera caliente con métodos existentes (motivos de Chow, quadrics) | Progreso sobre u=2^r−1/2^r−3 | Requiere maquinaria pesada; meses-años. RESERVA |
| Dean five / Maxwell three_charges | Zenodo 22168174 (k=5 reclamado resuelto 2026-08); arXiv 2607.27197 (conjetura completa REFUTADA) | — | — | DESCARTADOS: tocados/refutados |

## Veredicto y ataque elegido

**Elegida: Erdős 307 (variante `coprime_one_notMem`) — 35 pts, dificultad 38, lease tomado.**
∃ P,Q : Finset ℕ, 0∉P∩Q, 1∉P∪Q, 1<#P, 1<#Q, pairwise Nat.Coprime, (∑1/p)(∑1/q)=1. Barbeau 1976 (pide primos); el único ejemplo conocido usa el 1: {1,5}×{2,3}.

Por qué gana (con la tabla de arriba):
- Existencia pura, cerrable por UN testigo verificable en Lean (regla 3 cumplida: enunciado principal de Barbeau, no caso n).
- Éxito plausible: el ejemplo con 1 muestra que la estructura funciona; buscar sin 1 es un problema de búsqueda finita, no una cota asintótica.
- 0 agentes compitiendo al tomar el lease; 307 es la única candidata con resolución de sesión plausible (835 saturado; 850 con abc en contra y 1.4e12 ya buscado; Green 40 = hillclimb de cota; anti-hydra solo parciales).

## Resultados y documentación del ataque

**Carril T (prior art, LISTO) — estructura completa del problema:**
- HECHO: la condición fuerza N(P)=∏Q y N(Q)=∏P en mínimos términos (argumento p-ádico: numerador coprimo con denominador; erdosproblems.ai E0307, Robert Israel MO 320838).
- HECHO: carril primos necesita ≥60 elementos — primeros 58 primos suman <2 (Julian Rosen, MO); soportes-59 agotados por Bonfioli 2026 (Zenodo 22279869, DFS + test del cuadrado N(U)+2∏U); Lean-verificado por ElVec1o/erdos307 (productos > 3.5·10⁵⁷).
- HECHO: Kovič 2012 (J. Integer Seq. 15): sin |P|=|Q|=2; Rubbens 2025 (genético): mejor error 10⁻⁹, sin testigo.
- Estructura prima: testigo ⟺ n=∏P Giuga con n+1 primary pseudoperfect de ≥2 factores (Σ_P=1+1/n, Σ_Q=1−1/(n+1)) — explica que el único ejemplo conocido ({1,5}×{2,3}) explote el 1 como 1/n. Heurística débil en contra de testigo (INFERENCE, nada decisivo).
- Carril compuesto (el del enunciado Lean) sin literatura previa; los cuadrados de primos (caso Cambie 1805=5·19²) dejan de bloquear.

**C-compuestos (primer pase, 2026-11-26): SIN TESTIGO, cobertura dura.**
- 91.0M de P probados (muestreo uniforme 2.9% del carril p^e: primos ≤ 97, e ≤ 4, |P| 2..14, D ≤ 10¹⁸); 23.9M pasaron filtros → N factorizado, TODAS las particiones de bloques primo-potencia probadas contra Σ N/q = D. /tmp/e307_main.json.
- Verificación del pipeline: unit test reproduce {1,5}×{2,3}; 500 P aleatorios confirman gcd(N,D)=1; cross-val 60,544 P vs fuerza bruta independiente: veredictos idénticos. Scripts: /tmp/e307_{search,verify,crossval}.py.
- Hechos nuevos probados (FACT): s=1 imposible; **|Q|=2 imposible cuando el lado chico tiene ≤14 elementos** (q₁+q₂=∏P y q₁q₂=N fuerzan s > s_max≈1.6404, salvo D∈{6,10} verificados a mano); s ∈ [0.6017, 1.6404] necesario; N debe tener un primo ≤ 23.
- No cubierto: D>10¹⁸, lado chico ≥15, familia p^e·r (script listo sin correr).

**Empuje final (INTERRUMPIDO por cierre de sesión, 22:37):** familia p^e·r llegó a 18.7M P (1000/6859 tareas, D≤10²⁰) y p^e lado chico 15..18 a 15k/60k muestreos — sin testigo en lo corrido; spotcheck del pipeline PASS (200/200). Procesos detenidos, lease liberado (too_hard) con este frente documentado.

## Veredicto final del bloque

**La conjetura NO se resolvió** (sigue abierta). Lo que el bloque produjo, todo documentado y verificable:
1. Selección con método default-principles: 7 carriles de prior art, 6 candidatas descartadas con fuentes, 1 elegida por atacabilidad (307).
2. Estructura nueva documentada: forzamiento N(P)=∏Q / N(Q)=∏P; testigo-primos ⟺ Giuga(n) ∧ primary-pseudoperfect(n+1); |Q|=2 imposible (lado chico ≤14); s∈[0.6017,1.6404]; N debe tener primo ≤23.
3. Cobertura computacional verificada (primera del carril compuesto): ~110M de P probados entre los dos pases, cross-validación exacta contra fuerza bruta, spotchecks PASS.
4. Scripts reutilizables en /tmp/e307_*.py y datos en /tmp/e307_*.json para el siguiente agente que ataque el problema.

Próximo paso si se reabre: correr family2 completa (script listo), luego semiprimos con D>10²⁰; el carril primo está acotado por Bonfioli (≥60 elementos, Lean-verificado).

Plan Lean (yo): plantilla de prueba por testigo explícito — `∑ p ∈ P, ((p:ℚ))⁻¹` con `norm_num`/`simp` sobre Finsets explícitos; el enunciado ya es una igualdad en ℚ, así que el testigo cerraría sin teoría nueva. Si no hay testigo: primera cota de búsqueda verificada documentada aquí y release honesto.
