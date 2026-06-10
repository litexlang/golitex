# Copyright Jiachen Shen.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
# Litex email: <litexlang@outlook.com>
# Litex website: https://litexlang.com
# Litex github repository: https://github.com/litexlang/golitex
# Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

################################################################################
# Run This File to Generate the Logo of Litex
################################################################################

import turtle
import random
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont, ImageGrab

random.seed(0)
full_depth = 9
root_depth = 5
screen = None


def green_gradient(score):
    start_rgb = (0, 100, 0)  # dark green
    end_rgb = (144, 238, 144)  # light green
    normalized_score = score / 8
    r = int(start_rgb[0] + normalized_score * (end_rgb[0] - start_rgb[0]))
    g = int(start_rgb[1] + normalized_score * (end_rgb[1] - start_rgb[1]))
    b = int(start_rgb[2] + normalized_score * (end_rgb[2] - start_rgb[2]))
    return (r, g, b)


def draw_tree(t, branch_len, angle, depth):
    if depth == 0:
        return

    rgb = green_gradient(full_depth - depth)
    t.color(rgb[0] / 255, rgb[1] / 255, rgb[2] / 255)

    if depth > full_depth * 0.5:
        t.width(depth * 2)
    else:
        t.width(((depth * 2) + (full_depth * 0.5 * 2)) / 2)

    if depth >= full_depth * 0.8:
        t.forward(branch_len * 0.9)
    else:
        t.forward(branch_len)

    new_len = branch_len * (0.7 if depth > full_depth * 0.5 else 0.9)
    new_angle = angle * 0.9

    # right branch
    t.right(angle)
    draw_tree(t, new_len, new_angle, depth - 1)

    # left branch
    t.left(angle * 2)
    draw_tree(t, new_len, new_angle, depth - 1)

    t.right(angle)
    t.penup()
    t.backward(branch_len)
    t.pendown()


def draw_inverted_tree(t, branch_len, angle, depth):
    if depth == 0:
        return

    rgb = green_gradient(root_depth - depth)
    t.color(rgb[0] / 255, rgb[1] / 255, rgb[2] / 255)

    t.width(((full_depth - root_depth) + depth) * 2)

    random_factor = 1
    if depth != root_depth:
        t.forward(branch_len)

    new_len = branch_len * 0.85
    new_angle = angle * 0.9

    t.right(angle)
    draw_inverted_tree(t, new_len, new_angle * random_factor, depth - 1)

    t.left(angle * 2)
    draw_inverted_tree(t, new_len, new_angle * random_factor, depth - 1)

    t.right(angle)
    t.penup()
    t.backward(branch_len)
    t.pendown()


def draw_logo_screen():
    global screen

    screen = turtle.Screen()
    screen.setup(800, 800)  # Larger canvas size for more space
    screen.bgcolor(1.0, 0.95, 0.8)  # warm yellow background

    t = turtle.Turtle()
    t.speed(0)
    t.width(16)
    t.left(90)
    t.up()
    t.goto(0, -200)  # Adjust starting position for better centering
    t.down()

    # Draw main tree
    draw_tree(t, 150, 30, full_depth)

    # Draw inverted tree
    t.right(180)
    t.up()
    t.goto(0, -200)
    t.down()
    draw_inverted_tree(t, 50, 30, root_depth)

    t.hideturtle()
    screen.update()
    return screen


def save_image(filename="LiTeXNewLogo.PNG"):
    if screen is None:
        draw_logo_screen()

    canvas = screen.getcanvas()
    x = canvas.winfo_rootx()
    y = canvas.winfo_rooty()
    width = canvas.winfo_width()
    height = canvas.winfo_height()
    image = ImageGrab.grab((x, y, x + width, y + height))
    image.save(filename)
    print(f"{filename} saved")


def save_logo_with_text(
    base_filename="assets/logo.PNG",
    filename="assets/litex_logo_with_text.PNG",
    text="Litex",
):
    base_path = Path(base_filename)
    output_path = Path(filename)
    icon = Image.open(base_path).convert("RGBA")

    canvas_width = 1400
    canvas_height = 800
    background = (255, 244, 205, 255)
    canvas = Image.new("RGBA", (canvas_width, canvas_height), background)

    icon_size = 620
    icon = icon.resize((icon_size, icon_size), Image.Resampling.LANCZOS)
    icon_x = 90
    icon_y = (canvas_height - icon_size) // 2
    canvas.alpha_composite(icon, (icon_x, icon_y))

    draw = ImageDraw.Draw(canvas)
    font = load_text_logo_font(210)
    text_color = (18, 95, 35, 255)
    shadow_color = (126, 176, 94, 115)
    text_bbox = draw.textbbox((0, 0), text, font=font)
    text_width = text_bbox[2] - text_bbox[0]
    text_height = text_bbox[3] - text_bbox[1]
    text_x = 715
    text_y = (canvas_height - text_height) // 2 - 24

    draw.text((text_x + 6, text_y + 8), text, font=font, fill=shadow_color)
    draw.text((text_x, text_y), text, font=font, fill=text_color)

    underline_y = text_y + text_height + 34
    draw.rounded_rectangle(
        (text_x + 8, underline_y, text_x + text_width - 2, underline_y + 16),
        radius=8,
        fill=(50, 150, 66, 255),
    )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    canvas.save(output_path)
    print(f"{output_path} saved")


def load_text_logo_font(size):
    font_paths = [
        "/System/Library/Fonts/Supplemental/Avenir Next.ttc",
        "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
        "/Library/Fonts/Arial Bold.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    ]
    for font_path in font_paths:
        if Path(font_path).exists():
            return ImageFont.truetype(font_path, size=size)
    return ImageFont.load_default()


if __name__ == "__main__":
    save_logo_with_text()
