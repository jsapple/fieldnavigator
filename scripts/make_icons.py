"""Draw the Field Nav home-screen icons."""

from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

ROOT = Path(__file__).resolve().parents[1] / "icons"
FONT = Path(r"C:\Windows\Fonts\arialbd.ttf")
GREEN = (18, 54, 40, 255)
FIELD = (24, 74, 52, 255)
LIME = (214, 255, 74, 255)
INK = (244, 246, 240, 255)


def draw_icon(size: int, safe: float) -> Image.Image:
    image = Image.new("RGB", (size, size), GREEN)
    draw = ImageDraw.Draw(image)
    # Keep the mark inside the circle Android and iOS will crop.
    inner = size * safe
    left = (size - inner) / 2
    top = (size - inner) / 2
    draw.ellipse((left, top, left + inner, top + inner), fill=FIELD)

    cx = size / 2
    base = top + inner * 0.28
    stroke = max(2, int(size / 40))
    for index, width in enumerate((0.62, 0.44, 0.26)):
        y = base + index * inner * 0.07
        half = inner * width / 2
        box = (cx - half, y - half * 0.12, cx + half, y + half * 0.58)
        draw.arc(box, start=208, end=332, fill=LIME, width=stroke)

    font = ImageFont.truetype(str(FONT), int(inner * 0.38))
    text = "FN"
    box = draw.textbbox((0, 0), text, font=font)
    tw = box[2] - box[0]
    th = box[3] - box[1]
    x = (size - tw) / 2 - box[0]
    y = top + inner * 0.50 - box[1]
    draw.text((x, y), text, font=font, fill=INK)
    return image


def save(image: Image.Image, name: str, size: int | None = None) -> None:
    if size and size != image.size[0]:
        image = image.resize((size, size), Image.Resampling.LANCZOS)
    image.save(ROOT / name, "PNG")


def main() -> None:
    ROOT.mkdir(parents=True, exist_ok=True)
    full = draw_icon(512, 0.92)
    save(full, "icon-512.png")
    save(full, "icon-192.png", 192)
    save(full, "apple-touch-icon.png", 180)
    save(full, "favicon-32.png", 32)
    save(draw_icon(512, 0.68), "icon-maskable-512.png")


if __name__ == "__main__":
    main()
