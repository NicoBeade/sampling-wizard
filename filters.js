/* ═══════════════════════════════════════════════════════
   filters.js — Filter Design Engine
   Butterworth · Chebyshev I/II · Cauer · Bessel · Legendre
   ═══════════════════════════════════════════════════════ */
'use strict';

/* ─── §1 Math Utilities ─── */

function ellipticK(k) {
    if (Math.abs(k) < 1e-15) return Math.PI / 2;
    if (Math.abs(k) >= 1) return 1e18;
    let a = 1, b = Math.sqrt(1 - k * k);
    for (let i = 0; i < 60; i++) {
        const an = (a + b) / 2, bn = Math.sqrt(a * b);
        if (Math.abs(an - bn) < 1e-15) { a = an; break; }
        a = an; b = bn;
    }
    return Math.PI / (2 * a);
}

function ellipticKp(k) { return ellipticK(Math.sqrt(1 - k * k)); }

function jacobiSNCNDN(u, k) {
    if (Math.abs(k) < 1e-15) return { sn: Math.sin(u), cn: Math.cos(u), dn: 1 };
    if (k > 1 - 1e-15) {
        const th = Math.tanh(u), ch = 1 / Math.cosh(u);
        return { sn: th, cn: ch, dn: ch };
    }
    const N = 30, a = [1], c = [k], b = [Math.sqrt(1 - k * k)];
    for (let n = 0; n < N; n++) {
        a.push((a[n] + b[n]) / 2);
        c.push((a[n] - b[n]) / 2);
        b.push(Math.sqrt(a[n] * b[n]));
        if (Math.abs(c[c.length - 1]) < 1e-15) break;
    }
    const M = c.length - 1;
    let phi = Math.pow(2, M) * a[M] * u;
    for (let n = M; n > 0; n--) phi = (phi + Math.asin(c[n] * Math.sin(phi) / a[n])) / 2;
    const sn = Math.sin(phi), cn = Math.cos(phi), dn = Math.sqrt(1 - k * k * sn * sn);
    return { sn, cn, dn };
}

function jacobiCD(u, k) { const j = jacobiSNCNDN(u, k); return j.cn / j.dn; }

/* Complex arithmetic helpers */
const C = {
    mul: (a, b) => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re }),
    div: (a, b) => { const d = b.re * b.re + b.im * b.im; return { re: (a.re * b.re + a.im * b.im) / d, im: (a.im * b.re - a.re * b.im) / d }; },
    add: (a, b) => ({ re: a.re + b.re, im: a.im + b.im }),
    sub: (a, b) => ({ re: a.re - b.re, im: a.im - b.im }),
    abs2: (a) => a.re * a.re + a.im * a.im,
    abs: (a) => Math.sqrt(C.abs2(a)),
    conj: (a) => ({ re: a.re, im: -a.im }),
    neg: (a) => ({ re: -a.re, im: -a.im }),
    scale: (a, s) => ({ re: a.re * s, im: a.im * s }),
    fromReal: (r) => ({ re: r, im: 0 }),
};

/* Polynomial evaluation (coeffs highest-degree first) at complex z */
function polyEvalC(coeffs, z) {
    let r = { re: 0, im: 0 };
    for (let i = 0; i < coeffs.length; i++) {
        r = C.add(C.mul(r, z), typeof coeffs[i] === 'number' ? { re: coeffs[i], im: 0 } : coeffs[i]);
    }
    return r;
}

/* Durand-Kerner polynomial root finder (coeffs highest-degree first) */
function polyRoots(coeffs) {
    const n = coeffs.length - 1;
    if (n <= 0) return [];
    const a0 = coeffs[0];
    const c = coeffs.map(x => x / a0);
    const roots = [];
    const R = 1 + Math.max(...c.map(Math.abs));
    for (let k = 0; k < n; k++) {
        const ang = (2 * Math.PI * k / n) + 0.4;
        roots.push({ re: R * 0.9 * Math.cos(ang), im: R * 0.9 * Math.sin(ang) });
    }
    for (let iter = 0; iter < 200; iter++) {
        let maxD = 0;
        for (let k = 0; k < n; k++) {
            const p = polyEvalC(c.map(C.fromReal), roots[k]);
            let d = { re: 1, im: 0 };
            for (let j = 0; j < n; j++) { if (j !== k) d = C.mul(d, C.sub(roots[k], roots[j])); }
            const delta = C.div(p, d);
            roots[k] = C.sub(roots[k], delta);
            maxD = Math.max(maxD, C.abs(delta));
        }
        if (maxD < 1e-12) break;
    }
    // Clean up near-real roots
    for (const r of roots) { if (Math.abs(r.im) < 1e-10) r.im = 0; }
    return roots;
}

/* ─── §2 Bessel Polynomial Coefficients ─── */

function besselPoly(N) {
    // Reverse Bessel polynomial θ_N(s), returns coeffs [a_N, a_{N-1}, ..., a_0] (highest-degree first)
    if (N === 0) return [1];
    if (N === 1) return [1, 1];
    let prev2 = [1], prev1 = [1, 1];
    for (let n = 2; n <= N; n++) {
        const curr = new Array(n + 1).fill(0);
        const f = 2 * n - 1;
        for (let i = 0; i < prev1.length; i++) curr[i] += f * prev1[i]; // (2n-1)*θ_{n-1}
        for (let i = 0; i < prev2.length; i++) curr[i + 2] += prev2[i]; // s²*θ_{n-2}
        prev2 = prev1; prev1 = curr;
    }
    return prev1;
}

/* ─── §3 Prototype Poles/Zeros for Each Filter Type ─── */

function butterworthProto(N) {
    const poles = [];
    for (let k = 1; k <= N; k++) {
        const theta = Math.PI * (2 * k + N - 1) / (2 * N);
        poles.push({ re: Math.cos(theta), im: Math.sin(theta) });
    }
    return { poles, zeros: [] }; // normalized to |H(j*1)| = -3dB
}

function chebyshev1Proto(N, epsilonP) {
    const v = Math.asinh(1 / epsilonP) / N;
    const poles = [];
    for (let k = 1; k <= N; k++) {
        const phi = Math.PI * (2 * k - 1) / (2 * N);
        poles.push({ re: -Math.sinh(v) * Math.sin(phi), im: Math.cosh(v) * Math.cos(phi) });
    }
    return { poles, zeros: [] }; // normalized to passband edge ω_p = 1
}

function chebyshev2Proto(N, epsilonS) {
    // Compute Cheby I helper poles with ε_s, then invert
    const v = Math.asinh(epsilonS) / N;
    const poles = [], zeros = [];
    for (let k = 1; k <= N; k++) {
        const phi = Math.PI * (2 * k - 1) / (2 * N);
        const cosPhi = Math.cos(phi);
        // Zeros (on jω axis)
        if (Math.abs(cosPhi) > 1e-12) zeros.push({ re: 0, im: 1 / cosPhi });
        // Helper Cheby I pole
        const hRe = -Math.sinh(v) * Math.sin(phi);
        const hIm = Math.cosh(v) * cosPhi;
        // Invert: 1 / (hRe + j*hIm)
        const mag2 = hRe * hRe + hIm * hIm;
        poles.push({ re: hRe / mag2, im: -hIm / mag2 });
    }
    return { poles, zeros }; // normalized to stopband edge ω_s = 1
}

function cauerProto(N, epsilonP, epsilonS) {
    const k = 0.5; // fp/fa is always 0.5 since fa = 2*fp
    const K_val = ellipticK(k);
    const poles = [], zeros = [];
    const L = Math.floor(N / 2);
    // Zeros on jω axis
    for (let i = 1; i <= L; i++) {
        const u = (2 * i - 1) * K_val / N;
        const cd_val = jacobiCD(u, k);
        zeros.push({ re: 0, im: 1 / (k * cd_val) }); // in stopband (|ω|>1/k=2)
    }
    // Poles: use the relationship with Chebyshev-like mapping
    // Compute v0 parameter
    const k1 = epsilonP / epsilonS;
    const K1 = ellipticK(k1);
    const K1p = ellipticKp(k1);
    const Kp = ellipticKp(k);
    const v0 = K_val / (N * K1) * computeV0Helper(epsilonP, k1, K1);
    for (let i = 1; i <= L; i++) {
        const u = (2 * i - 1) * K_val / N;
        const { sn: snU, cn: cnU, dn: dnU } = jacobiSNCNDN(u, k);
        const { sn: snV, cn: cnV, dn: dnV } = jacobiSNCNDN(v0, Math.sqrt(1 - k * k));
        const denom = 1 - (dnU * snV) * (dnU * snV);
        const pRe = -(cnU * dnU * snV * cnV) / denom;
        const pIm = (snU * dnV) / denom;
        poles.push({ re: pRe, im: pIm });
        poles.push({ re: pRe, im: -pIm });
    }
    if (N % 2 === 1) {
        const { sn: snV, cn: cnV } = jacobiSNCNDN(v0, Math.sqrt(1 - k * k));
        poles.push({ re: -snV * cnV / (1 - snV * snV), im: 0 });
    }
    // Include conjugate zeros
    const fullZeros = [];
    for (const z of zeros) {
        fullZeros.push(z);
        fullZeros.push(C.conj(z));
    }
    return { poles, zeros: fullZeros };
}

function computeV0Helper(epsilonP, k1, K1) {
    // v0 = sn^{-1}(1/εp, k1') / K(k1')  where k1' = sqrt(1-k1²)
    // Using Newton iteration on sn(v*K1p, k1p) = 1/εp
    const k1p = Math.sqrt(1 - k1 * k1);
    const K1p = ellipticK(k1p);
    const target = Math.min(1 / epsilonP, 0.999 / 1); // clamp
    // Binary search for v such that sn(v, k1p) = target
    let lo = 0, hi = K1p;
    for (let i = 0; i < 60; i++) {
        const mid = (lo + hi) / 2;
        const { sn } = jacobiSNCNDN(mid, k1p);
        if (sn < target) lo = mid; else hi = mid;
    }
    return (lo + hi) / 2;
}

function besselProto(N) {
    const coeffs = besselPoly(N);
    const roots = polyRoots(coeffs);
    // roots are the poles. Already in LHP for Bessel polynomials.
    // Normalize to -3dB at ω=1: find ω_3dB and scale poles
    const dc = coeffs[coeffs.length - 1]; // θ_N(0)
    // Binary search for ω where |θ_N(0)/θ_N(jω)| = 1/√2
    let lo = 0.1, hi = 10;
    for (let i = 0; i < 60; i++) {
        const mid = (lo + hi) / 2;
        const val = polyEvalC(coeffs.map(C.fromReal), { re: 0, im: mid });
        const mag = dc / C.abs(val);
        if (mag > 1 / Math.SQRT2) lo = mid; else hi = mid;
    }
    const w3dB = (lo + hi) / 2;
    // Scale all poles so -3dB is at ω=1
    const poles = roots.map(r => ({ re: r.re / w3dB, im: r.im / w3dB }));
    return { poles, zeros: [] };
}

function legendreProto(N) {
    // Papoulis (Optimal L) filter: build |H(jω)|² polynomial, find poles
    // |H(jω)|² = 1/(1 + ε²*L_N(ω²)) where L_N(x) = x^N * Σ binom(N-1+k,k)*(1-x)^k
    // For -3dB normalization, ε² is chosen so |H(j*1)|² = 0.5
    // First compute L_N(1) to find ε²: L_N(1) = 1^N * binom(N-1,0) = 1 → ε² = 1
    // Build the polynomial 1 + L_N(-s²) and find roots
    // L_N(x) as polynomial in x:
    const LN = new Array(2 * N).fill(0); // degree up to 2N-1
    for (let k = 0; k < N; k++) {
        const binom = binomial(N - 1 + k, k);
        // x^N * (1-x)^k: expand (1-x)^k then multiply by x^N
        const expansion = expandBinomialNeg(k); // coeffs of (1-x)^k in ascending powers of x
        for (let j = 0; j <= k; j++) {
            const deg = N + j; // x^(N+j)
            if (deg < 2 * N) LN[deg] += binom * expansion[j];
        }
    }
    // Now LN[i] is the coefficient of x^i in L_N(x)
    // D(s)*D(-s) = 1 + ε² * L_N(-s²), with ε²=1 for -3dB at ω=1
    // Substitute x = -s²: x^i = (-s²)^i = (-1)^i * s^{2i}
    const polyDeg = 2 * (2 * N - 1); // could be up to s^{4N-2}, but actually up to s^{2*(2N-1)}
    const dCoeffs = new Array(2 * N + 1).fill(0);
    dCoeffs[0] = 1; // constant term
    for (let i = 0; i < 2 * N; i++) {
        if (Math.abs(LN[i]) < 1e-18) continue;
        // x^i → (-1)^i * s^{2i}: coefficient index in poly is 2*i (in ascending s powers)
        // But we need highest-degree-first for polyRoots, so build ascending first then reverse
        const sign = (i % 2 === 0) ? 1 : -1;
        dCoeffs[2 * i] = (dCoeffs[2 * i] || 0) + sign * LN[i];
    }
    // Trim and reverse to highest-degree first
    let maxDeg = dCoeffs.length - 1;
    while (maxDeg > 0 && Math.abs(dCoeffs[maxDeg]) < 1e-18) maxDeg--;
    const polyHDF = [];
    for (let i = maxDeg; i >= 0; i--) polyHDF.push(dCoeffs[i] || 0);

    const roots = polyRoots(polyHDF);
    // Select left-half-plane roots with Re < 0
    const poles = roots.filter(r => r.re < -1e-10);
    return { poles, zeros: [] };
}

function binomial(n, k) {
    if (k < 0 || k > n) return 0;
    if (k === 0 || k === n) return 1;
    let r = 1;
    for (let i = 0; i < k; i++) r = r * (n - i) / (i + 1);
    return r;
}

function expandBinomialNeg(k) {
    // (1 - x)^k: returns coefficients in ascending powers of x [c_0, c_1, ..., c_k]
    const c = new Array(k + 1);
    for (let i = 0; i <= k; i++) c[i] = binomial(k, i) * ((i % 2 === 0) ? 1 : -1);
    return c;
}

/* ─── §4 Minimum Order Computation ─── */

function epsFromDb(dB) { return Math.sqrt(Math.pow(10, Math.abs(dB) / 10) - 1); }

function computeMinOrder(type, Gp, Ga) {
    const ep = epsFromDb(Gp), ea = epsFromDb(Ga);
    const ratio = ea / ep;
    const Ws = 2; // fa/fp = 2 always
    switch (type) {
        case 'butterworth':
            return Math.ceil(Math.log(ratio) / Math.log(Ws));
        case 'chebyshev1':
        case 'chebyshev2':
            return Math.ceil(Math.acosh(ratio) / Math.acosh(Ws));
        case 'cauer': {
            const k = 1 / Ws; // = 0.5
            const k1 = ep / ea;
            const num = ellipticK(k) * ellipticKp(k1);
            const den = ellipticKp(k) * ellipticK(k1);
            return Math.ceil(num / den);
        }
        case 'bessel': {
            // Iterative: increase N until Bessel of order N meets Ga at Ws
            const coeffs0 = besselPoly(1);
            for (let N = 1; N <= 25; N++) {
                const proto = besselProto(N);
                // Evaluate magnitude at ω = Ws (normalized to -3dB at 1)
                const mag = evalPrototypeMag(proto, Ws);
                const attenDb = -20 * Math.log10(mag);
                if (attenDb >= Math.abs(Ga)) return N;
            }
            return 25;
        }
        case 'legendre': {
            for (let N = 1; N <= 25; N++) {
                const proto = legendreProto(N);
                const mag = evalPrototypeMag(proto, Ws);
                const attenDb = -20 * Math.log10(mag);
                if (attenDb >= Math.abs(Ga)) return N;
            }
            return 25;
        }
        default: return 2;
    }
}

function evalPrototypeMag(proto, omega) {
    // |H(jω)| for an all-pole prototype with known poles (normalized)
    // H(s) = K / Π(s - p_k), dc gain = 1
    let numMag = 1, denMag = 1;
    const s = { re: 0, im: omega };
    for (const p of proto.poles) {
        denMag *= C.abs(C.sub(s, p));
    }
    for (const z of proto.zeros) {
        numMag *= C.abs(C.sub(s, z));
    }
    // DC gain normalization: evaluate at s=0
    let dcDen = 1, dcNum = 1;
    for (const p of proto.poles) dcDen *= C.abs(C.neg(p));
    for (const z of proto.zeros) dcNum *= C.abs(C.neg(z));
    return (numMag / denMag) * (dcDen / dcNum);
}

/* ─── §5 Analog-to-Digital: Bilinear Transform → SOS ─── */

function designFilter(type, fp, Gp, Ga, sampleRate) {
    const ep = epsFromDb(Gp), ea = epsFromDb(Ga);
    const N = computeMinOrder(type, Gp, Ga);
    if (N <= 0) return { sos: [], order: 0 };

    // Get analog prototype poles/zeros
    let proto;
    switch (type) {
        case 'butterworth': proto = butterworthProto(N); break;
        case 'chebyshev1': proto = chebyshev1Proto(N, ep); break;
        case 'chebyshev2': proto = chebyshev2Proto(N, ea); break;
        case 'cauer': proto = cauerProto(N, ep, ea); break;
        case 'bessel': proto = besselProto(N); break;
        case 'legendre': proto = legendreProto(N); break;
        default: proto = butterworthProto(N);
    }

    // For Cheby II, prototype is normalized to stopband = 1, scale to passband
    // For others, normalized to passband = 1 (or -3dB = 1)
    // Pre-warp cutoff
    const warpedFp = (2 * sampleRate) * Math.tan(Math.PI * fp / sampleRate);

    // Scale poles/zeros to desired frequency
    const scaledPoles = proto.poles.map(p => C.scale(p, warpedFp));
    const scaledZeros = proto.zeros.map(z => C.scale(z, warpedFp));

    // Bilinear transform: s → 2*fs*(z-1)/(z+1)
    // For pole p: z = (1 + p/(2*fs)) / (1 - p/(2*fs))
    const T = 2 * sampleRate;
    const digPoles = scaledPoles.map(p => C.div(C.add({ re: T, im: 0 }, p), C.sub({ re: T, im: 0 }, p)));
    const digZeros = scaledZeros.map(z => C.div(C.add({ re: T, im: 0 }, z), C.sub({ re: T, im: 0 }, z)));

    // Fill remaining zeros at z = -1 (from s = ∞)
    while (digZeros.length < digPoles.length) digZeros.push({ re: -1, im: 0 });

    // Group into second-order sections
    const sos = groupIntoSOS(digPoles, digZeros, scaledPoles, scaledZeros, T);
    return { sos, order: N };
}

function groupIntoSOS(poles, zeros, aPoles, aZeros, T) {
    // Pair conjugate poles and zeros into biquad sections
    const usedP = new Array(poles.length).fill(false);
    const usedZ = new Array(zeros.length).fill(false);
    const sections = [];

    // Find conjugate pairs of poles
    const polePairs = [];
    for (let i = 0; i < poles.length; i++) {
        if (usedP[i]) continue;
        if (Math.abs(poles[i].im) < 1e-10) {
            polePairs.push([i, -1]); // real pole
            usedP[i] = true;
        } else {
            // Find conjugate
            for (let j = i + 1; j < poles.length; j++) {
                if (!usedP[j] && Math.abs(poles[i].re - poles[j].re) < 1e-8 && Math.abs(poles[i].im + poles[j].im) < 1e-8) {
                    polePairs.push([i, j]);
                    usedP[i] = usedP[j] = true;
                    break;
                }
            }
            if (!usedP[i]) { polePairs.push([i, -1]); usedP[i] = true; } // orphaned
        }
    }

    // Similarly for zeros
    const zeroPairs = [];
    for (let i = 0; i < zeros.length; i++) {
        if (usedZ[i]) continue;
        if (Math.abs(zeros[i].im) < 1e-10) {
            zeroPairs.push([i, -1]);
            usedZ[i] = true;
        } else {
            for (let j = i + 1; j < zeros.length; j++) {
                if (!usedZ[j] && Math.abs(zeros[i].re - zeros[j].re) < 1e-8 && Math.abs(zeros[i].im + zeros[j].im) < 1e-8) {
                    zeroPairs.push([i, j]);
                    usedZ[i] = usedZ[j] = true;
                    break;
                }
            }
            if (!usedZ[i]) { zeroPairs.push([i, -1]); usedZ[i] = true; }
        }
    }

    // Merge single poles/zeros into pairs for biquads
    const realPoleIdxs = polePairs.filter(p => p[1] === -1);
    const conjPolePairs = polePairs.filter(p => p[1] !== -1);
    const realZeroIdxs = zeroPairs.filter(z => z[1] === -1);
    const conjZeroPairs = zeroPairs.filter(z => z[1] !== -1);

    // Build biquad from conjugate pole pair + conjugate zero pair
    for (let i = 0; i < conjPolePairs.length; i++) {
        const [p1] = conjPolePairs[i];
        const zp = conjZeroPairs.length > i ? conjZeroPairs[i] : null;
        const section = makeBiquad(poles[p1], zp ? zeros[zp[0]] : { re: -1, im: 0 }, true);
        sections.push(section);
    }

    // Pair remaining real poles
    for (let i = 0; i < realPoleIdxs.length; i += 2) {
        const p1 = poles[realPoleIdxs[i][0]];
        const p2 = (i + 1 < realPoleIdxs.length) ? poles[realPoleIdxs[i + 1][0]] : null;
        const rz = realZeroIdxs.length > 0 ? zeros[realZeroIdxs.shift()[0]] : { re: -1, im: 0 };
        const rz2 = p2 && realZeroIdxs.length > 0 ? zeros[realZeroIdxs.shift()[0]] : { re: -1, im: 0 };
        if (p2) {
            // Two real poles → one biquad
            const a1 = -(p1.re + p2.re), a2 = p1.re * p2.re;
            const b1 = -(rz.re + rz2.re), b2 = rz.re * rz2.re;
            sections.push({ b: [1, b1, b2], a: [1, a1, a2] });
        } else {
            // Single real pole → first-order section stored as biquad
            sections.push({ b: [1, -rz.re, 0], a: [1, -p1.re, 0] });
        }
    }

    // Normalize DC gain to 1
    for (const s of sections) {
        const dcNum = s.b[0] + s.b[1] + s.b[2];
        const dcDen = s.a[0] + s.a[1] + s.a[2];
        if (Math.abs(dcDen) > 1e-15 && Math.abs(dcNum) > 1e-15) {
            const gain = dcDen / dcNum;
            s.b[0] *= gain; s.b[1] *= gain; s.b[2] *= gain;
        }
    }

    return sections;
}

function makeBiquad(pole, zero, conjugate) {
    // Conjugate pair of poles: (z - p)(z - p*) = z² - 2*Re(p)*z + |p|²
    const a1 = -2 * pole.re;
    const a2 = pole.re * pole.re + pole.im * pole.im;
    let b1, b2;
    if (conjugate && Math.abs(zero.im) > 1e-10) {
        b1 = -2 * zero.re;
        b2 = zero.re * zero.re + zero.im * zero.im;
    } else {
        // zeros at -1: (z+1)² = z² + 2z + 1
        b1 = 2; b2 = 1;
    }
    return { b: [1, b1, b2], a: [1, a1, a2] };
}

/* ─── §6 Apply SOS Filter to Signal ─── */

function applySOS(signal, sos) {
    let s = signal;
    for (const sec of sos) s = applyBiquadSection(s, sec);
    return s;
}

function applyBiquadSection(signal, sec) {
    const n = signal.length;
    const out = new Float64Array(n);
    const [b0, b1, b2] = sec.b;
    const a1 = sec.a[1], a2 = sec.a[2];
    let x1 = 0, x2 = 0, y1 = 0, y2 = 0;
    for (let i = 0; i < n; i++) {
        const x = signal[i];
        const y = b0 * x + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2;
        out[i] = y;
        x2 = x1; x1 = x; y2 = y1; y1 = y;
    }
    return out;
}

function freqResponseFull(sos, nPoints, sampleRate, maxFreq) {
    const mags = new Float64Array(nPoints);
    const phases = new Float64Array(nPoints);
    const groupDelays = new Float64Array(nPoints);
    for (let i = 0; i < nPoints; i++) {
        const f = (i / nPoints) * maxFreq;
        const w = 2 * Math.PI * f / sampleRate;
        let totalMagSq = 1, totalPhase = 0;
        for (const sec of sos) {
            const cosW = Math.cos(w), sinW = Math.sin(w);
            const cos2W = Math.cos(2 * w), sin2W = Math.sin(2 * w);
            const numRe = sec.b[0] + sec.b[1] * cosW + sec.b[2] * cos2W;
            const numIm = -sec.b[1] * sinW - sec.b[2] * sin2W;
            const denRe = 1 + sec.a[1] * cosW + sec.a[2] * cos2W;
            const denIm = -sec.a[1] * sinW - sec.a[2] * sin2W;
            totalMagSq *= (numRe * numRe + numIm * numIm) / (denRe * denRe + denIm * denIm + 1e-30);
            totalPhase += Math.atan2(numIm, numRe) - Math.atan2(denIm, denRe);
        }
        mags[i] = 10 * Math.log10(Math.max(totalMagSq, 1e-24));
        phases[i] = totalPhase;
    }
    for (let i = 1; i < nPoints; i++) {
        let d = phases[i] - phases[i - 1];
        while (d > Math.PI) d -= 2 * Math.PI;
        while (d < -Math.PI) d += 2 * Math.PI;
        phases[i] = phases[i - 1] + d;
    }
    for (let i = 0; i < nPoints; i++) phases[i] *= 180 / Math.PI;
    const dw = (2 * Math.PI * maxFreq) / (nPoints * sampleRate);
    for (let i = 0; i < nPoints; i++) {
        let dp;
        if (i === 0) dp = (phases[1] - phases[0]) * Math.PI / 180;
        else if (i === nPoints - 1) dp = (phases[i] - phases[i - 1]) * Math.PI / 180;
        else dp = (phases[i + 1] - phases[i - 1]) * Math.PI / 180 / 2;
        groupDelays[i] = Math.max(-dp / dw * 1000 / sampleRate, 0);
    }
    return { mags, phases, groupDelays, maxFreq };
}
