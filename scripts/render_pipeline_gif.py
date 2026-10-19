#!/usr/bin/env python3
"""Render docs/assets/pipeline.gif — the pontifex architecture animation.

The diagram is code, not a hand-edited binary: run this script to regenerate the
GIF and the static preview PNG. Requires Pillow (dev dependency).
"""

from __future__ import annotations

from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "docs" / "assets"
W, H = 1200, 780

# ---------------------------------------------------------------------------
# Palette and fonts
# ---------------------------------------------------------------------------

BG = (9, 13, 24, 255)
BG2 = (13, 20, 36, 255)
PANEL = (18, 25, 40, 255)
PANEL2 = (22, 31, 50, 255)
BORDER = (46, 61, 92, 255)
TEXT = (228, 234, 246, 255)
MUTED = (148, 163, 184, 255)
FAINT = (100, 116, 145, 255)
CYAN = (34, 211, 238, 255)
BLUE = (96, 165, 250, 255)
GREEN = (52, 211, 153, 255)
AMBER = (251, 191, 36, 255)
PINK = (244, 114, 182, 255)

FONT_DIR = Path("/System/Library/Fonts/Supplemental")
if not (FONT_DIR / "Andale Mono.ttf").exists():  # portable fallback
    FONT_DIR = Path("/usr/share/fonts/truetype/dejavu")

def font(name: str, size: int):
    candidates = {
        "mono": ["Andale Mono.ttf", "DejaVuSansMono.ttf"],
        "body": ["Arial.ttf", "DejaVuSans.ttf"],
        "bold": ["Arial Bold.ttf", "DejaVuSans-Bold.ttf"],
    }[name]
    for candidate in candidates:
        path = FONT_DIR / candidate
        if path.exists():
            return ImageFont.truetype(str(path), size)
    return ImageFont.load_default(size=size)

F_TITLE = font("bold", 36)
F_SUB = font("body", 18)
F_LABEL = font("bold", 15)
F_BOX = font("bold", 17)
F_BODY = font("body", 15)
F_SMALL = font("body", 13)
F_MONO = font("mono", 14)
F_MONO_S = font("mono", 13)
F_MONO_XS = font("mono", 12)
F_STAT = font("bold", 15)


# ---------------------------------------------------------------------------
# Small drawing helpers
# ---------------------------------------------------------------------------


def lerp_color(a, b, t: float):
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(4))


def clamp(x: float) -> float:
    return max(0.0, min(1.0, x))


def ease(t: float) -> float:
    t = clamp(t)
    return t * t * (3 - 2 * t)


def fade(t: float, start: float, dur: float) -> float:
    return ease((t - start) / dur)


def new_layer():
    return Image.new("RGBA", (W, H), (0, 0, 0, 0))


def composite(base: Image.Image, layer: Image.Image, alpha: float):
    if alpha <= 0:
        return
    if alpha < 1:
        layer.putalpha(layer.getchannel("A").point(lambda v: int(v * alpha)))
    base.alpha_composite(layer)


def box(layer, rect, fill=PANEL, outline=BORDER, width=1, radius=12):
    draw = ImageDraw.Draw(layer)
    draw.rounded_rectangle(rect, radius=radius, fill=fill, outline=outline, width=width)


def text(layer, xy, value, font_obj, fill=TEXT, anchor="la"):
    ImageDraw.Draw(layer).text(xy, value, font=font_obj, fill=fill, anchor=anchor)


def mono_lines(layer, xy, lines, font_obj=F_MONO, fill=TEXT, leading=19, colors=None):
    draw = ImageDraw.Draw(layer)
    x, y = xy
    for index, line in enumerate(lines):
        color = colors[index] if colors and index < len(colors) and colors[index] else fill
        draw.text((x, y + index * leading), line, font=font_obj, fill=color)


def arrow(layer, start, end, color=CYAN, width=2, progress=1.0, head=7):
    if progress <= 0:
        return
    draw = ImageDraw.Draw(layer)
    x0, y0 = start
    x1, y1 = end
    xm = x0 + (x1 - x0) * clamp(progress)
    ym = y0 + (y1 - y0) * clamp(progress)
    draw.line((x0, y0, xm, ym), fill=color, width=width)
    if progress > 0.92:
        dx, dy = x1 - x0, y1 - y0
        length = max(1.0, (dx * dx + dy * dy) ** 0.5)
        ux, uy = dx / length, dy / length
        px, py = -uy, ux
        draw.polygon(
            [
                (x1, y1),
                (x1 - ux * head * 1.6 + px * head, y1 - uy * head * 1.6 + py * head),
                (x1 - ux * head * 1.6 - px * head, y1 - uy * head * 1.6 - py * head),
            ],
            fill=color,
        )


def check(layer, x, y, color=GREEN, scale=1.0):
    draw = ImageDraw.Draw(layer)
    draw.line((x, y + 6 * scale, x + 4 * scale, y + 10 * scale), fill=color, width=2)
    draw.line((x + 4 * scale, y + 10 * scale, x + 12 * scale, y), fill=color, width=2)


def base_background() -> Image.Image:
    """A flat background keeps text crisp and GIF palettes small."""
    img = Image.new("RGBA", (W, H), BG)
    draw = ImageDraw.Draw(img)
    draw.line((0, 104, W, 104), fill=(46, 61, 92, 150), width=1)
    draw.line((0, 482, W, 482), fill=(46, 61, 92, 100), width=1)
    draw.line((0, 714, W, 714), fill=(46, 61, 92, 100), width=1)
    return img


BASE = base_background()

# ---------------------------------------------------------------------------
# Content
# ---------------------------------------------------------------------------

STAGES = [
    ("1 · Python source", "examples/*.py", "one scalar function", CYAN),
    ("2 · Core AST", "ids, desugared", "assign · if · while", BLUE),
    ("3 · SSA IR", "slots · phis · headers", "structured & typed", PINK),
    ("4 · Lean code", "direct or certified", "Rat · binary64", AMBER),
    ("5 · Proofs & specs", "physics · bounds", "kernel-checked goals", GREEN),
]

VERIFY = [
    ("<fn>_lowering", "AST → IR agreement", "rfl"),
    ("<fn>_link", "straight-line code = IR", "rfl"),
    ("<fn>_compiled_link", "if / while, every fuel + Ops", "induction"),
    ("#audit_axioms", "only propext · choice · Quot", "build gate"),
]

PYTHON_LINES = [
    "def step(x, v, a, dt):",
    "    v = v + a * dt",
    "    x = x + v * dt",
    "    return x, v",
]
IR_LINES = [
    "seq [",
    "  assign 4 (add slot1 (mul slot2 slot3))",
    "  assign 5 (add slot0 (mul slot4 slot3))",
    "  ret [slot5, slot4] ]",
]
LEAN_LINES = [
    "def step (x v a dt : Rat) : Option (Rat × Rat) :=",
    "  let v1 := v + a * dt;",
    "  let x1 := x + v1 * dt;",
    "  some (x1, v1)",
    "",
    "theorem step_link (x v a dt : Rat) :",
    "    step 64 x v a dt =",
    "      (Outcome.toOption (Fn.run Ops.rat stepIR 64 [x,v,a,dt]))",
    "        .map (fun vs => (vs[0]!, vs[1]!)) := rfl",
]

# ---------------------------------------------------------------------------
# Frame rendering
# ---------------------------------------------------------------------------


def render(t: float) -> Image.Image:
    img = BASE.copy()

    # ---- header ----------------------------------------------------------
    a = fade(t, 0.0, 0.6)
    layer = new_layer()
    text(layer, (42, 26), "Pontifex", F_TITLE, TEXT)
    text(layer, (212, 38), "Python → Lean 4 verification bridge", F_SUB, MUTED)
    text(layer, (44, 72), "A kernel-checked translation pipeline for a scalar Python subset", F_BODY, FAINT)
    composite(img, layer, a)

    badges = [("no Mathlib", CYAN), ("no ring tactic", PINK), ("no sorry", GREEN)]
    for index, (label, color) in enumerate(badges):
        la = fade(t, 0.55 + index * 0.12, 0.4)
        layer = new_layer()
        x = 792 + index * 128
        box(layer, (x, 30, x + 116, 58), fill=PANEL, outline=color, width=1, radius=14)
        text(layer, (x + 58, 44), label, F_SMALL, color, anchor="mm")
        composite(img, layer, la)

    # ---- pipeline --------------------------------------------------------
    left, top, bw, bh, gap = 40, 118, 208, 106, 27
    centers = []
    for index, (title, line1, line2, color) in enumerate(STAGES):
        start = 0.9 + index * 0.34
        la = fade(t, start, 0.42)
        x = left + index * (bw + gap)
        centers.append((x + bw // 2, top + bh // 2))
        if la > 0:
            flash = max(0.0, 1.0 - (t - start) / 0.8)
            outline = lerp_color(BORDER, color, flash)
            width = 2 if flash > 0.05 else 1
            layer = new_layer()
            box(layer, (x, top, x + bw, top + bh), fill=PANEL, outline=outline, width=width, radius=12)
            draw = ImageDraw.Draw(layer)
            draw.rectangle((x + 1, top + 1, x + 5, top + bh - 1), fill=color)
            text(layer, (x + 16, top + 16), title, F_BOX, TEXT)
            text(layer, (x + 16, top + 46), line1, F_SMALL, MUTED)
            text(layer, (x + 16, top + 68), line2, F_MONO_XS, FAINT)
            composite(img, layer, la)

        if index < len(STAGES) - 1:
            pa = fade(t, start + 0.22, 0.5)
            layer = new_layer()
            x0 = x + bw + 4
            x1 = x + bw + gap - 4
            arrow(layer, (x0, top + bh // 2), (x1, top + bh // 2), color=FAINT, width=2, progress=pa)
            composite(img, layer, pa)

    # ---- verification lane ----------------------------------------------
    label_alpha = fade(t, 2.9, 0.5)
    layer = new_layer()
    text(layer, (42, 248), "KERNEL-CHECKED, PER PROGRAM", F_LABEL, GREEN)
    composite(img, layer, label_alpha)

    vleft, vtop, vw, vh, vgap = 40, 274, 268, 90, 18
    for index, (name, desc, tag) in enumerate(VERIFY):
        start = 3.0 + index * 0.34
        la = fade(t, start, 0.42)
        if la <= 0:
            continue
        x = vleft + index * (vw + vgap)
        flash = max(0.0, 1.0 - (t - start) / 0.7)
        layer = new_layer()
        box(layer, (x, vtop, x + vw, vtop + vh), fill=PANEL2,
            outline=lerp_color(BORDER, GREEN, flash), width=2 if flash > 0.05 else 1)
        check(layer, x + 14, vtop + 16, GREEN)
        text(layer, (x + 34, vtop + 12), name, F_MONO_S, TEXT)
        text(layer, (x + 14, vtop + 40), desc, F_SMALL, MUTED)
        box(layer, (x + vw - 86, vtop + 58, x + vw - 12, vtop + 80), fill=(14, 45, 40, 255),
            outline=(30, 90, 75, 255), radius=10)
        text(layer, (x + vw - 49, vtop + 69), tag, F_MONO_XS, GREEN, anchor="mm")
        composite(img, layer, la)

        # connector from the relevant pipeline stage
        source = [1, 2, 2, 4][index]
        sx, sy = centers[source]
        ca = fade(t, start + 0.15, 0.45)
        layer = new_layer()
        dash_y0, dash_y1 = top + bh + 4, vtop - 4
        y = dash_y0
        while y < dash_y0 + (dash_y1 - dash_y0) * ca:
            ImageDraw.Draw(layer).line((sx, y, sx, min(y + 5, dash_y1)), fill=(60, 78, 110, 255), width=1)
            y += 9
        composite(img, layer, ca)

    # ---- trust lanes -----------------------------------------------------
    trust_alpha = fade(t, 4.55, 0.55)
    layer = new_layer()
    box(layer, (40, 384, 590, 478), fill=(38, 28, 14, 255), outline=(120, 82, 24, 255), radius=12)
    text(layer, (56, 398), "TRUSTED + TESTED", F_LABEL, AMBER)
    text(layer, (56, 422), "ast.parse · surface desugaring · AST transcription", F_SMALL, (226, 200, 150, 255))
    text(layer, (56, 444), "native Float/CPU rounding · CPython oracle", F_SMALL, (226, 200, 150, 255))
    text(layer, (56, 462), "differential harness catches drift here", F_MONO_XS, (184, 150, 96, 255))
    composite(img, layer, trust_alpha)

    kernel_alpha = fade(t, 4.85, 0.55)
    layer = new_layer()
    box(layer, (610, 384, 1160, 478), fill=(12, 40, 33, 255), outline=(28, 96, 77, 255), radius=12)
    text(layer, (626, 398), "KERNEL-CHECKED", F_LABEL, GREEN)
    text(layer, (626, 422), "lowering agreement · code ↔ IR · outcomes & fuel", F_SMALL, (170, 230, 205, 255))
    text(layer, (626, 444), "physics specs · Float bit/value tiers · axiom audit", F_SMALL, (170, 230, 205, 255))
    text(layer, (626, 462), "every certificate is replayed by lake build", F_MONO_XS, (120, 186, 160, 255))
    composite(img, layer, kernel_alpha)

    # ---- code panes ------------------------------------------------------
    py_alpha = fade(t, 5.5, 0.5)
    layer = new_layer()
    box(layer, (40, 496, 600, 604), fill=PANEL, outline=BORDER, radius=12)
    text(layer, (56, 506), "Python", F_LABEL, CYAN)
    mono_lines(layer, (56, 526), PYTHON_LINES, F_MONO_S, TEXT, leading=18)
    composite(img, layer, py_alpha)

    ir_alpha = fade(t, 5.9, 0.5)
    layer = new_layer()
    box(layer, (40, 612, 600, 706), fill=PANEL, outline=BORDER, radius=12)
    text(layer, (56, 620), "SSA IR", F_LABEL, PINK)
    mono_lines(layer, (56, 642), IR_LINES, F_MONO_XS, MUTED, leading=15)
    composite(img, layer, ir_alpha)

    lean_alpha = fade(t, 6.35, 0.55)
    layer = new_layer()
    box(layer, (620, 496, 1160, 706), fill=PANEL, outline=BORDER, radius=12)
    text(layer, (636, 506), "Lean 4", F_LABEL, GREEN)
    colors = [TEXT, TEXT, TEXT, TEXT, None, CYAN, TEXT, TEXT, GREEN]
    mono_lines(layer, (636, 530), LEAN_LINES, F_MONO_XS, TEXT, leading=17, colors=colors)
    composite(img, layer, lean_alpha)

    # ---- footer ----------------------------------------------------------
    foot_alpha = fade(t, 7.15, 0.5)
    layer = new_layer()
    box(layer, (40, 720, 230, 756), fill=(12, 40, 33, 255), outline=(28, 96, 77, 255), radius=10)
    text(layer, (135, 738), "make check", F_MONO_S, GREEN, anchor="mm")
    stats = [
        "330 tests",
        "100k Float patterns",
        "57 rejection snapshots",
        "0 sorry · 0 project axioms",
    ]
    x = 252
    for stat in stats:
        text(layer, (x, 730), stat, F_SMALL, MUTED)
        x += 236
    composite(img, layer, foot_alpha)

    # final pulse / scan line
    if t > 7.6:
        pulse = 0.5 + 0.5 * ((t * 1.7) % 1.0)
        layer = new_layer()
        draw = ImageDraw.Draw(layer)
        x = 40 + (W - 80) * ((t * 0.22) % 1.0)
        draw.line((x, 110, x, 480), fill=(34, 211, 238, int(40 + 60 * pulse)), width=2)
        composite(img, layer, 1.0)

    return img.convert("RGB")


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    fps = 7
    duration = 8.6
    raw = [render(i / fps) for i in range(int(duration * fps) + 1)]
    palette_source = raw[-1].quantize(colors=64, method=Image.Quantize.MEDIANCUT)
    frames = [
        f.quantize(palette=palette_source, dither=Image.Dither.NONE) for f in raw
    ]
    gif_path = OUT / "pipeline.gif"
    frames[0].save(
        gif_path,
        save_all=True,
        append_images=frames[1:],
        duration=int(1000 / fps),
        loop=0,
        optimize=False,
        disposal=2,
    )
    render(7.4).save(OUT / "pipeline.png")
    print(f"wrote {gif_path} ({gif_path.stat().st_size / 1e6:.2f} MB) and pipeline.png")


if __name__ == "__main__":
    main()
