#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib>=3.8", "numpy>=1.26"]
# ///
"""Generate two full-width publication-grade vector plots (Figures 1 and 2 of
matmul_9_4_constant.tex) with an identical shared legend:

  Figure 1 (figures/bounds_vs_exponent.{pdf,png}):
      Base-10 logarithm of the base block side (log10 V or log10 v_k, on a log
      vertical scale) vs. target matrix multiplication exponent tau.

  Figure 2 (figures/scaling_vs_excess.{pdf,png}):
      The same universal lower bounds and constructive achievability curves on
      doubly logarithmic axes vs. the exponent excess delta = tau - 9/4.

Run:
    uv run verification/plot_bounds.py

Every curve point is computed directly from the exact algebraic recurrences and
universal inequalities proved in matmul_9_4_constant.tex (Sections 3 and 4) and
cross-checked against the printed benchmark values of Tables 2--4.
"""
from __future__ import annotations

import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import LogLocator, NullFormatter
import numpy as np


# ============================================================================
# Exact algebraic evaluators (matching Sections 3--4 of matmul_9_4_constant.tex)
# ============================================================================
def log_exact_Md(c: int, d: int) -> float:
    """Natural log of exact balanced-word count M_d(c) = sum_{h=0}^d (C(d,h)(c+1)^{d-h})^2."""
    if d <= 600:
        lg_d = math.lgamma(d + 1)
        lc1 = math.log(c + 1)
        terms = [
            2.0 * (lg_d - math.lgamma(h + 1) - math.lgamma(d - h + 1) + (d - h) * lc1)
            for h in range(d + 1)
        ]
        m = max(terms)
        return m + math.log(sum(math.exp(x - m) for x in terms))
    p_b = 1.0 / (c + 2.0)
    return 2.0 * d * math.log(c + 2.0) - 0.5 * math.log(4.0 * math.pi * d * p_b * (1.0 - p_b))


def exact_Lk_log2m1(c: int, k: int) -> float:
    """Compute ln(2 L_k(c) - 1) using exact recurrence for k <= 3000 and sharp sandwich above."""
    if k <= 3000:
        L = 1
        for _ in range(k):
            L += (3 * L - 1 + (c - 2)) // (c - 1)
        return math.log(2 * L - 1)
    return math.log(2.0 * c / 3.0) + k * math.log((c + 2.0) / (c - 1.0))


def candidate_c_grid(tau: float, mult_hi: float = 5.0) -> list[int]:
    delta = tau - 2.25
    c_start = max(2, int(9.0 / (8.0 * delta)) - 2)
    c_end = max(c_start + 35, int(mult_hi / delta) + 12)
    cs = list(range(c_start, min(c_start + 55, c_end + 1)))
    if c_end > c_start + 55:
        for i in range(65):
            cs.append(int(round(c_start * (c_end / c_start) ** (i / 64.0))))
    return sorted(set(cs))


def optimize_unimodal_int(fn, d_lo: int, d_hi: int) -> float:
    """Fast integer ternary + multi-scale probe minimization for convex-like d objectives."""
    best = fn(d_lo)
    d_best = d_lo
    for frac in np.geomspace(1.0, max(1.05, d_hi / max(1, d_lo)), 28):
        d = max(d_lo, min(d_hi, int(round(d_lo * frac))))
        v = fn(d)
        if v < best:
            best, d_best = v, d
    a = max(d_lo, int(d_best * 0.65))
    b = max(d_best + 6, int(d_best * 1.50))
    while b - a > 4:
        m1 = a + (b - a) // 3
        m2 = b - (b - a) // 3
        if fn(m1) < fn(m2):
            b = m2
        else:
            a = m1
    for d in range(a, b + 1):
        v = fn(d)
        if v < best:
            best = v
    return best


def find_min_valid_d(cond_fn, d_guess: int) -> int:
    hi = max(8, d_guess)
    while not cond_fn(hi):
        hi *= 2
        if hi > 10**12:
            return hi
    lo = 1
    while lo < hi:
        mid = (lo + hi) // 2
        if cond_fn(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def pass_pre_lb_ub(tau: float) -> tuple[float, float]:
    """Sharp universal LB (Eqs. sharp_denom--sharp_k_lnLam_lb) and constructive UB for log10(v_k)."""
    delta = tau - 2.25
    ln10 = math.log(10.0)
    best_lb = 1e100
    best_ub = 1e100
    for c in candidate_c_grid(tau, 5.2):
        ln_rho = math.log((c + 2.0) / (c - 1.0))
        ln_g = math.log((c + 2.0) / c)
        if 1.5 * ln_rho / ln_g >= tau:
            continue
        j0 = (c - 1) // 3
        BL_full = max(0.0, math.log(2 * j0 + 1) - j0 * ln_rho)

        def del_ub(d: int) -> tuple[float, float]:
            lu = 4.0 * d * ln_g - 2.0 * math.log(d + 1.0)
            return tau * lu - 6.0 * d * ln_rho - math.log(64.0), lu

        d_min = find_min_valid_d(lambda d: del_ub(d)[0] > 0.0, max(10, int(20 * c / delta)))

        def eval_lb(d: int) -> float:
            du, lu = del_ub(d)
            if du <= 0.0 or lu <= 0.0:
                return 1e100
            ln_w = 2.0 * d * math.log(c + 2.0) - math.log(d + 1.0)
            BL = BL_full if ((9.0 - 2.0 * tau) * ln_w / du >= j0) else 0.0
            return (2.0 * ln_w + ((9.0 - 2.0 * tau) * ln_w + 6.0 * d * BL) / (du / lu)) / ln10

        def eval_ub(d: int) -> float:
            du, lu = del_ub(d)
            if du <= 0.0 or lu <= 0.0:
                return 1e100
            ln_w = 2.0 * d * math.log(c + 2.0) - math.log(d + 1.0)
            k_hi = max(1, math.ceil(((9.0 - 2.0 * tau) * ln_w + 6.0 * d * math.log(2.0 * c / 3.0)) / du))
            if k_hi <= 2500:
                L = 1
                k_best = k_hi
                for k_cur in range(1, k_hi + 1):
                    L += (3 * L - 1 + (c - 2)) // (c - 1)
                    lhs = (9.0 - 2.0 * tau) * ln_w + k_cur * math.log(64.0) + 6.0 * d * math.log(2 * L - 1)
                    if lhs < k_cur * tau * lu:
                        k_best = k_cur
                        break
                k_hi = k_best
            return (2.0 * ln_w + k_hi * lu) / ln10

        v_lb = optimize_unimodal_int(eval_lb, d_min, max(d_min + 20, int(d_min * 6)))
        v_ub = optimize_unimodal_int(eval_ub, d_min, max(d_min + 20, int(d_min * 6)))
        if v_lb < best_lb:
            best_lb = v_lb
        if v_ub < best_ub:
            best_ub = v_ub
    return best_lb, best_ub


def pass_post_lb_ub(tau: float, use_exact_Md: bool = False) -> tuple[float, float]:
    """Sharp universal LB (literal Pass) and constructive UB for post-Bini log10(V)."""
    delta = tau - 2.25
    ln10 = math.log(10.0)
    best_lb = 1e100
    best_ub = 1e100
    for c in candidate_c_grid(tau, 4.8):
        ln_rho = math.log((c + 2.0) / (c - 1.0))
        ln_g = math.log((c + 2.0) / c)
        if 1.5 * ln_rho / ln_g >= tau:
            continue
        j0 = (c - 1) // 3
        BL_full = max(0.0, math.log(2 * j0 + 1) - j0 * ln_rho)

        def ln_w_fn(d: int) -> float:
            if use_exact_Md:
                return log_exact_Md(c, d)
            return 2.0 * d * math.log(c + 2.0) - math.log(d + 1.0)

        def del_ub(d: int) -> tuple[float, float, float]:
            ln_w = ln_w_fn(d)
            lu = 2.0 * (ln_w - 2.0 * d * math.log(c))
            return tau * lu - 6.0 * d * ln_rho - math.log(64.0), lu, ln_w

        d_min = find_min_valid_d(lambda d: del_ub(d)[0] > 0.0, max(10, int(20 * c / delta)))

        def eval_lb(d: int) -> float:
            du, lu, ln_w = del_ub(d)
            if du <= 0.0 or lu <= 0.0:
                return 1e100
            BL = BL_full if ((9.0 - 2.0 * tau) * ln_w / du >= j0) else 0.0
            kc = ((9.0 - 2.0 * tau) * ln_w + 6.0 * d * BL) / du
            ln_S = math.log(3.0 * (2 * d + 1)) + ln_w
            k_star = kc + math.sqrt(max(1e-12, kc * kc - 0.5 * kc))
            ln_lam_lb = (6.0 * d * ln_rho + math.log(64.0)) / tau
            return ((2.0 * k_star - 1.0) * ln_S / ((k_star - kc) * du)) * (2.0 * ln_w + k_star * ln_lam_lb) / ln10

        def eval_ub(d: int) -> float:
            du, lu, ln_w = del_ub(d)
            if du <= 0.0 or lu <= 0.0:
                return 1e100
            kc_ub = ((9.0 - 2.0 * tau) * ln_w + 6.0 * d * math.log(2.0 * c / 3.0)) / du
            ln_S = math.log(3.0 * (2 * d + 1)) + ln_w
            best_k = 1e100
            for mult in (1.45, 1.65, 1.85, 2.0, 2.2, 2.5):
                kk = max(math.ceil(kc_ub) + 1, int(round(mult * kc_ub)))
                ln_2Lk1 = exact_Lk_log2m1(c, kk)
                M = kk * (tau * lu - math.log(64.0)) - (9.0 - 2.0 * tau) * ln_w - 6.0 * d * ln_2Lk1
                if M <= 0.0:
                    continue
                ln_E = math.log(2.0) + 2.0 * kk * ln_S
                h = max(1, math.ceil((ln_E + math.log(max(2.0, ln_E / M + 2.0))) / M))
                while math.log(h) + ln_E >= h * M:
                    h += 1
                v = h * (2.0 * ln_w + kk * lu) / ln10
                if v < best_k:
                    best_k = v
            return best_k

        if not use_exact_Md:
            v_lb = optimize_unimodal_int(eval_lb, d_min, max(d_min + 25, int(d_min * 7)))
            if v_lb < best_lb:
                best_lb = v_lb
        v_ub = optimize_unimodal_int(eval_ub, d_min, max(d_min + 25, int(d_min * 7)))
        if v_ub < best_ub:
            best_ub = v_ub
    return best_lb, best_ub


def str3_single_matrix_ub(tau: float) -> float | None:
    """Single-matrix post-Bini log10(V_single) for untwisted Str_3^{otimes N} (Lemma 4.3)."""
    floor_str3 = 3.0 * math.log(4.0) / math.log(6.0)
    if tau <= floor_str3 + 5e-4:
        return None
    ln10 = math.log(10.0)
    best = 1e100
    Ns = list(range(8, 120, 2)) + list(range(120, 600, 6)) + list(range(600, 3200, 20))
    for N in Ns:
        lnM = math.lgamma(N + 1) - 2.0 * math.lgamma(N // 2 + 1)
        lnv = N * math.log(3.0) + lnM
        lnp = 3.0 * lnM
        ln_2m1 = math.log(2.0) + lnM + math.log1p(-0.5 * math.exp(-lnM))
        lnr = 3.0 * ln_2m1 + 3.0 * N * math.log(4.0)
        margin = tau * lnv - (lnr - lnp)
        if margin <= 0.0:
            continue
        lnE = math.log(3.0 * (N + 1)) + lnM
        h_lo = max(1, int(math.ceil(lnE / margin)))
        for h in range(h_lo, h_lo + 45):
            lhs = math.log(h) + lnE + math.log1p(math.exp(-(math.log(h) + lnE)))
            rem = h * margin - lhs
            if rem <= 0.0:
                continue
            r_sch = max(1, math.ceil((h * lnp) / rem))
            while r_sch * rem <= h * lnp:
                r_sch += 1
            val = h * r_sch * lnv / ln10
            if val < best:
                best = val
    return best if best < 1e99 else None


def shared_legend_handles(c_post: str, c_opt: str, c_pre: str, c_str3: str, c_slope: str) -> list[Line2D]:
    """Identical line-and-marker legend used on both Figure 1 and Figure 2.
    Solid lines for universal LBs, strokeless open circles for achievable UBs,
    no filled boxes, and no redundant style words in the labels.
    """
    return [
        Line2D([0], [0], color=c_post, linestyle="-", lw=2.1,
               label=r"Pass post-Bini $V$ (universal LB)"),
        Line2D([0], [0], color="none", marker="o", markersize=6.6,
               markerfacecolor="none", markeredgecolor=c_post, markeredgewidth=1.55,
               label=r"Pass post-Bini $V$ (achievable UB)"),
        Line2D([0], [0], color=c_opt, linestyle="-.", lw=1.85,
               label="Optimized Pass ($M_d$ + Lü) post-Bini UB"),
        Line2D([0], [0], color=c_pre, linestyle="-", lw=2.1,
               label=r"Pass pre-Bini $v_k$ (universal LB)"),
        Line2D([0], [0], color="none", marker="o", markersize=6.6,
               markerfacecolor="none", markeredgecolor=c_pre, markeredgewidth=1.55,
               label=r"Pass pre-Bini $v_k$ (achievable UB)"),
        Line2D([0], [0], color=c_str3, linestyle="-", lw=2.1,
               label=r"Untwisted $\mathrm{Str}_3^{\otimes N}$ single-matrix UB"),
        Line2D([0], [0], color="none", marker="s", markersize=6.8,
               markerfacecolor="#f48c36", markeredgecolor="#444444", markeredgewidth=0.9,
               label=r"Pan (1978): $V=70,\ \tau=2.795$"),
        Line2D([0], [0], color="none", marker="^", markersize=7.4,
               markerfacecolor="#f5c542", markeredgecolor="#444444", markeredgewidth=0.9,
               label=r"Strassen (1969): $V=2,\ \tau=2.807$"),
        Line2D([0], [0], color="none", marker="D", markersize=6.8,
               markerfacecolor="white", markeredgecolor="#4a5568", markeredgewidth=1.4,
               label=r"Supermult. obstruction: $V=16,\ R=513$"),
        Line2D([0], [0], color=c_slope, linestyle=":", lw=1.45,
               label=r"Asymptotic $\delta^{-5}(\ln\delta^{-1})^3$"),
        Line2D([0], [0], color=c_slope, linestyle=(0, (3, 2, 1, 2)), lw=1.4,
               label=r"Asymptotic $\delta^{-3}(\ln\delta^{-1})^2$"),
    ]


def configure_y_axis(ax: plt.Axes) -> None:
    ax.set_yscale("log")
    ax.set_ylim(0.08, 6.0e22)
    ax.set_ylabel(r"Base-10 log of block side ($\log_{10} V$ or $\log_{10} v_k$)")
    ax.grid(True, which="major", linestyle=":", linewidth=0.6, color="#cbd5e1", alpha=0.8)
    ax.yaxis.set_major_locator(LogLocator(base=10.0, subs=(1.0,), numticks=14))
    ax.yaxis.set_minor_locator(LogLocator(base=10.0, subs=(1.0,), numticks=25))
    ax.yaxis.set_minor_formatter(NullFormatter())
    for spine in ax.spines.values():
        spine.set_color("#475569")


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    fig_dir = root / "figures"
    fig_dir.mkdir(parents=True, exist_ok=True)

    # Dense exponent grid spanning [2.251, 2.800] including all benchmark targets
    taus = np.array([
        2.251, 2.252, 2.254, 2.257, 2.260, 2.265, 2.275, 2.285, 2.300,
        2.321, 2.340, 2.371, 2.410, 2.450, 2.500, 2.560, 2.630, 2.695,
        2.750, 2.800,
    ])
    deltas = taus - 2.25

    pre_lb, pre_ub = [], []
    post_lb, post_ub, opt_ub = [], [], []
    for t in taus:
        plb, pub = pass_pre_lb_ub(float(t))
        qlb, qub = pass_post_lb_ub(float(t), use_exact_Md=False)
        _, oub = pass_post_lb_ub(float(t), use_exact_Md=True)
        pre_lb.append(plb)
        pre_ub.append(pub)
        post_lb.append(qlb)
        post_ub.append(qub)
        opt_ub.append(oub)

    pre_lb = np.array(pre_lb)
    pre_ub = np.array(pre_ub)
    post_lb = np.array(post_lb)
    post_ub = np.array(post_ub)
    opt_ub = np.array(opt_ub)

    # Sanity-check exact agreement with printed benchmark tables (Tables 2--4)
    idx_2800 = int(np.argmin(np.abs(taus - 2.800)))
    idx_2371 = int(np.argmin(np.abs(taus - 2.371)))
    idx_2251 = int(np.argmin(np.abs(taus - 2.251)))
    assert 7100 < pre_lb[idx_2800] < 7300, f"pre_lb(2.800)={pre_lb[idx_2800]}"
    assert 7800 < pre_ub[idx_2800] < 8100, f"pre_ub(2.800)={pre_ub[idx_2800]}"
    assert 9.3e5 < post_lb[idx_2800] < 9.7e5, f"post_lb(2.800)={post_lb[idx_2800]}"
    assert 6.0e9 < post_lb[idx_2371] < 6.3e9, f"post_lb(2.371)={post_lb[idx_2371]}"
    assert 2.0e21 < post_lb[idx_2251] < 2.2e21, f"post_lb(2.251)={post_lb[idx_2251]}"

    # Untwisted Str_3^{otimes N} single-matrix curve above 3*log_6(4) ~ 2.32112
    taus_s3 = np.array([
        2.326, 2.330, 2.336, 2.345, 2.358, 2.371, 2.395, 2.430,
        2.465, 2.500, 2.550, 2.620, 2.695, 2.750, 2.800, 2.807,
    ])
    vals_s3 = np.array([str3_single_matrix_ub(float(t)) for t in taus_s3])

    # Concrete exact algorithms & obstruction witness
    tau_strassen = math.log2(7.0)
    log10_V_strassen = math.log10(2.0)
    tau_pan = math.log(143640.0) / math.log(70.0)
    log10_V_pan = math.log10(70.0)
    tau_obs = 2.251
    log10_V_obs = math.log10(16.0)

    # Asymptotic reference slope guides (Theorem thm:asymptotic_scaling)
    d_ref = np.geomspace(1.3e-3, 0.22, 80)
    g_post = 6.0 * (d_ref ** -5.0) * (np.log(1.0 / d_ref) ** 3)
    g_pre = 0.085 * (d_ref ** -3.0) * (np.log(1.0 / d_ref) ** 2)

    # ========================================================================
    # Publication styling: lighter, luminous editorial palette
    # ========================================================================
    plt.rcParams.update({
        "font.family": "serif",
        "mathtext.fontset": "cm",
        "font.size": 10.5,
        "axes.labelsize": 11.5,
        "axes.titlesize": 12.0,
        "legend.fontsize": 8.6,
        "xtick.labelsize": 9.8,
        "ytick.labelsize": 9.8,
        "axes.linewidth": 0.9,
        "lines.linewidth": 2.0,
    })

    c_post = "#e85d75"      # bright coral-rose (Pass post-Bini)
    c_opt = "#9d6bd4"       # soft orchid-violet (Optimized Pass M_d + Lu)
    c_pre = "#3b8eea"       # luminous sky-azure (Pass pre-Bini)
    c_str3 = "#2eb872"      # fresh emerald-mint (Untwisted Str_3)
    c_ref = "#7b8794"       # soft slate gray (vertical thresholds)
    c_slope = "#64748b"     # cool slate (asymptotic guides)

    handles = shared_legend_handles(c_post, c_opt, c_pre, c_str3, c_slope)

    # Visually well-spaced open-marker subsets (prevent marker crowding near 2.251)
    # taus indices: 0=2.251, 2=2.254, 4=2.260, 6=2.275, 8=2.300, 9=2.321,
    #               11=2.371, 12=2.410, 13=2.450, 14=2.500, 15=2.560, 16=2.630,
    #               17=2.695, 18=2.750, 19=2.800
    idx_f1 = [0, 2, 4, 6, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19]
    idx_f2 = [0, 1, 2, 4, 5, 6, 8, 9, 11, 12, 14, 15, 17, 19]

    # ========================================================================
    # FIGURE 1: Universal lower bounds and achievability vs. exponent tau
    # ========================================================================
    fig1, ax1 = plt.subplots(figsize=(8.8, 5.8))

    # Universal LBs as crisp solid lines; achievable UBs as strokeless open circles
    ax1.plot(taus, post_lb, color=c_post, linestyle="-", lw=2.1, zorder=3)
    ax1.plot(taus[idx_f1], post_ub[idx_f1], color=c_post, linestyle="none",
             marker="o", markersize=6.8, markerfacecolor="none",
             markeredgecolor=c_post, markeredgewidth=1.55, zorder=5)
    ax1.plot(taus, opt_ub, color=c_opt, linestyle="-.", lw=1.8, zorder=3)

    ax1.plot(taus, pre_lb, color=c_pre, linestyle="-", lw=2.1, zorder=3)
    ax1.plot(taus[idx_f1], pre_ub[idx_f1], color=c_pre, linestyle="none",
             marker="o", markersize=6.8, markerfacecolor="none",
             markeredgecolor=c_pre, markeredgewidth=1.55, zorder=5)

    ax1.plot(taus_s3, vals_s3, color=c_str3, linestyle="-", lw=2.1, zorder=3)

    # Subtle asymptotic reference guides mapped to tau = 9/4 + delta
    ax1.plot(2.25 + d_ref, g_post, color=c_slope, linestyle=":", lw=1.25, alpha=0.8, zorder=2)
    ax1.plot(2.25 + d_ref, g_pre, color=c_slope, linestyle=(0, (3, 2, 1, 2)), lw=1.2, alpha=0.8, zorder=2)

    ax1.scatter([tau_pan], [log10_V_pan], color="#f48c36", edgecolor="#444444", lw=0.9, s=62, zorder=6, marker="s")
    ax1.scatter([tau_strassen], [log10_V_strassen], color="#f5c542", edgecolor="#444444", lw=0.9, s=72, zorder=6, marker="^")
    ax1.scatter([tau_obs], [log10_V_obs], facecolor="white", edgecolor="#4a5568", lw=1.5, s=70, zorder=6, marker="D")

    vlines = [
        (2.250, r"$\omega = 9/4$", "#e05a6d", ":", 1.15, 0.005, 1.8e18),
        (3 * math.log(4) / math.log(6), r"$3\log_6 4 \approx 2.321$", c_str3, ":", 1.05, 0.004, 0.8e0),
        (2.371, r"CW/AE", c_ref, ":", 0.9, 0.004, 0.6e0),
        (2.500, r"Slabbing", c_ref, ":", 0.9, 0.004, 0.6e0),
    ]
    for xv, lbl, col, ls, lw, dx, yv in vlines:
        ax1.axvline(xv, color=col, linestyle=ls, linewidth=lw, alpha=0.72, zorder=1)
        ax1.text(xv + dx, yv, lbl, color=col, fontsize=8.5, rotation=90, va="bottom", ha="left")

    configure_y_axis(ax1)
    ax1.set_xlim(2.235, 2.835)
    ax1.set_xlabel(r"Target matrix multiplication exponent $\tau$")
    ax1.set_title(r"Universal lower bounds and constructive achievability vs. exponent $\tau$")

    ax1.annotate(r"Post-Bini $V$" + "\n" + r"($10^{2.1\times 10^{21}}$ at $2.251$)",
                 xy=(2.262, post_lb[4]), xytext=(2.415, 2.5e19),
                 fontsize=9.0, color="#c9405b",
                 arrowprops=dict(arrowstyle="->", color="#c9405b", lw=1.0, connectionstyle="arc3,rad=0.14"))
    ax1.annotate(r"Pre-Bini $v_k$",
                 xy=(2.288, pre_lb[7]), xytext=(2.410, 2.5e13),
                 fontsize=9.0, color="#2473cc",
                 arrowprops=dict(arrowstyle="->", color="#2473cc", lw=1.0, connectionstyle="arc3,rad=0.12"))
    ax1.annotate(r"Pan ($V{=}70$)" + "\n" + r"Strassen ($V{=}2$)",
                 xy=(tau_pan - 0.005, log10_V_pan * 1.15), xytext=(2.615, 2.5e1),
                 fontsize=8.6, color="#8a5a19",
                 arrowprops=dict(arrowstyle="->", color="#8a5a19", lw=0.95, connectionstyle="arc3,rad=0.12"))
    ax1.annotate(r"$V{=}16$" + "\n" + r"$R{=}513$",
                 xy=(tau_obs + 0.002, log10_V_obs * 1.55), xytext=(2.258, 2.0e2),
                 fontsize=8.3, color="#334155",
                 bbox=dict(facecolor="white", edgecolor="none", alpha=0.82, pad=0.7),
                 arrowprops=dict(arrowstyle="->", color="#334155", lw=0.9, connectionstyle="arc3,rad=0.14"))

    fig1.legend(
        handles=handles,
        loc="lower center", ncol=3, frameon=True, framealpha=0.96,
        edgecolor="#cbd5e1", bbox_to_anchor=(0.5, 0.012),
        columnspacing=1.1, handlelength=2.2,
    )
    fig1.subplots_adjust(left=0.105, right=0.98, top=0.93, bottom=0.31)

    f1_pdf = fig_dir / "bounds_vs_exponent.pdf"
    f1_png = fig_dir / "bounds_vs_exponent.png"
    fig1.savefig(f1_pdf, format="pdf")
    fig1.savefig(f1_png, dpi=220)
    plt.close(fig1)

    # ========================================================================
    # FIGURE 2: Doubly logarithmic power-law scaling vs. excess delta = tau - 9/4
    # ========================================================================
    fig2, ax2 = plt.subplots(figsize=(8.8, 5.8))

    ax2.plot(deltas, post_lb, color=c_post, linestyle="-", lw=2.1, zorder=3)
    ax2.plot(deltas[idx_f2], post_ub[idx_f2], color=c_post, linestyle="none",
             marker="o", markersize=6.8, markerfacecolor="none",
             markeredgecolor=c_post, markeredgewidth=1.55, zorder=5)
    ax2.plot(deltas, opt_ub, color=c_opt, linestyle="-.", lw=1.8, zorder=3)

    ax2.plot(deltas, pre_lb, color=c_pre, linestyle="-", lw=2.1, zorder=3)
    ax2.plot(deltas[idx_f2], pre_ub[idx_f2], color=c_pre, linestyle="none",
             marker="o", markersize=6.8, markerfacecolor="none",
             markeredgecolor=c_pre, markeredgewidth=1.55, zorder=5)

    ax2.plot(taus_s3 - 2.25, vals_s3, color=c_str3, linestyle="-", lw=2.1, zorder=3)

    ax2.plot(d_ref, g_post, color=c_slope, linestyle=":", lw=1.4, zorder=2)
    ax2.plot(d_ref, g_pre, color=c_slope, linestyle=(0, (3, 2, 1, 2)), lw=1.35, zorder=2)

    ax2.scatter([tau_pan - 2.25], [log10_V_pan], color="#f48c36", edgecolor="#444444", lw=0.9, s=62, zorder=6, marker="s")
    ax2.scatter([tau_strassen - 2.25], [log10_V_strassen], color="#f5c542", edgecolor="#444444", lw=0.9, s=72, zorder=6, marker="^")
    ax2.scatter([tau_obs - 2.25], [log10_V_obs], facecolor="white", edgecolor="#4a5568", lw=1.5, s=70, zorder=6, marker="D")

    ax2.text(2.4e-3, 2.2e14, r"$\propto \delta^{-5}(\ln\delta^{-1})^3$",
             fontsize=9.2, color="#475569", rotation=-27.5, ha="left", va="top")
    ax2.text(2.4e-3, 5.5e6, r"$\propto \delta^{-3}(\ln\delta^{-1})^2$",
             fontsize=9.2, color="#475569", rotation=-17.0, ha="left", va="top")

    configure_y_axis(ax2)
    ax2.set_xscale("log")
    ax2.set_xlim(7.2e-4, 0.80)
    ax2.set_xlabel(r"Exponent excess $\delta = \tau - 9/4$ (log scale)")
    ax2.set_title(r"Asymptotic power-law scaling vs. excess $\delta = \tau - 9/4$")

    fig2.legend(
        handles=handles,
        loc="lower center", ncol=3, frameon=True, framealpha=0.96,
        edgecolor="#cbd5e1", bbox_to_anchor=(0.5, 0.012),
        columnspacing=1.1, handlelength=2.2,
    )
    fig2.subplots_adjust(left=0.105, right=0.98, top=0.93, bottom=0.31)

    f2_pdf = fig_dir / "scaling_vs_excess.pdf"
    f2_png = fig_dir / "scaling_vs_excess.png"
    fig2.savefig(f2_pdf, format="pdf")
    fig2.savefig(f2_png, dpi=220)
    plt.close(fig2)

    print(f"Wrote {f1_pdf} ({f1_pdf.stat().st_size} bytes) and {f1_png} ({f1_png.stat().st_size} bytes)")
    print(f"Wrote {f2_pdf} ({f2_pdf.stat().st_size} bytes) and {f2_png} ({f2_png.stat().st_size} bytes)")
    print(f"Verified benchmarks: tau=2.800 preLB={pre_lb[idx_2800]:.2f} preUB={pre_ub[idx_2800]:.2f} "
          f"postLB={post_lb[idx_2800]:.3e} postUB={post_ub[idx_2800]:.3e}")
    print(f"                     tau=2.371 preLB={pre_lb[idx_2371]:.2f} postLB={post_lb[idx_2371]:.3e}")
    print(f"                     tau=2.251 preLB={pre_lb[idx_2251]:.3e} postLB={post_lb[idx_2251]:.3e}")


if __name__ == "__main__":
    main()
