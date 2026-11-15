"""Insert the illustrative N=6 Chebyshev curve into the slide source.

Sampling is for the figure only. The all-horizon result is proved in the paper.
Python standard library only. No random numbers or optimization computations.
"""
from pathlib import Path
import math

root = Path(__file__).resolve().parent
N = 6
M = 2 * N + 1
left, width, center, scale = 1.2, 6.35, 4.1, 17
curve = []
for j in range(1201):
    u = j / 1200
    q = (-1) ** N * math.cos(M * math.acos(u)) / M
    curve.append(f"({left + width * u:.6f},{center + scale * q:.6f})")
parts = [r"\draw[->,Line,line width=1pt] (1.05,4.1)--(7.85,4.1);"]
for sign in [-1, 1]:
    y = center + sign * scale / M
    parts.append(f"\\draw[densely dashed,Muted] ({left},{y:.6f})--({left+width},{y:.6f});")
parts.append(r"\draw[Blue,line width=2.2pt] plot coordinates {" + " ".join(curve) + "};")
for i in range(N + 1):
    u = math.cos(i * math.pi / M)
    q = (-1) ** (N + i) / M
    parts.append(f"\\fill[Teal] ({left+width*u:.6f},{center+scale*q:.6f}) circle (.045);")
parts += [
    r"\node[text=Muted,font=\fontsize{18}{22}\selectfont] at (1.2,3.75) {$0$};",
    r"\node[text=Muted,font=\fontsize{18}{22}\selectfont] at (7.55,3.75) {$1$};",
    r"\node[text=Muted,font=\fontsize{20}{24}\selectfont] at (7.85,4.38) {$u$};",
    r"\node[anchor=west,text=Muted,font=\fontsize{17}{20}\selectfont] at (1.2,5.68) {$1/(2N+1)$};",
]
source = (root / "slides.tex").read_text()
assert source.count("% CHEB_PLOT") == 1
(root.parent / "memory-slides.tex").write_text(source.replace("% CHEB_PLOT", "\n".join(parts)))
print("Wrote memory-slides.tex with 1201 Chebyshev samples; N=6, L=1.")
