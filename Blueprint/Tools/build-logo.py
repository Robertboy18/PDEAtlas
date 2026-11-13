#!/usr/bin/env python3
"""Prepare the supplied wordmark for the site's light and dark backgrounds."""

from pathlib import Path

import numpy as np
from PIL import Image, ImageFilter


def main():
    blueprint = Path(__file__).resolve().parents[1]
    source = Image.open(blueprint / "logo.png").convert("RGB")
    # The source is the wordmark on a white canvas, 318 pixels high, with the
    # symbol in its first 440 columns.
    pixels = np.asarray(source, dtype=np.float32)
    darkness = 255 - pixels.min(axis=2)
    warmth = (pixels[:, :, 0] - pixels[:, :, 2]) / np.maximum(darkness, 1)
    ink = Image.fromarray((pixels.max(axis=2) < 105).astype("uint8") * 255)
    near_ink = np.asarray(ink.filter(ImageFilter.MaxFilter(15))) > 0
    lettering = near_ink & (warmth < 0.12)

    # Remove the white matte, including antialiased edges. Gold needs a separate
    # opacity scale so the pale surface stays visible on a dark page.
    alpha = np.where(
        lettering,
        np.clip((darkness - 3) / 225, 0, 1),
        np.clip((darkness - 3) / 20, 0, 1),
    )
    foreground = np.clip(
        (pixels - 255 * (1 - alpha[:, :, None]))
        / np.maximum(alpha[:, :, None], 0.001),
        0,
        255,
    )
    dark = foreground.copy()
    dark[lettering] = [247, 244, 236]
    destination = blueprint / "Assets" / "Brand"
    destination.mkdir(parents=True, exist_ok=True)
    for theme, colors in [("light", foreground), ("dark", dark)]:
        rgba = np.dstack((colors, alpha * 255)).round().clip(0, 255).astype("uint8")
        image = Image.fromarray(rgba, "RGBA")
        image.save(destination / f"logo-{theme}.webp", quality=93, method=6)
        if theme == "light":
            # The symbol stays legible on a small, opaque paper-coloured tile.
            symbol = image.crop((0, 0, 440, 318))
            tile = Image.new("RGB", (464, 464), "#fffdf8")
            tile.paste(symbol, (12, 73), symbol.getchannel("A"))
            tile.resize((64, 64), Image.Resampling.LANCZOS).save(
                destination / "favicon.png", optimize=True
            )


if __name__ == "__main__":
    main()
