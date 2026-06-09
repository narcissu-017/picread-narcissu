# Layout Algorithm Notes

This document describes the three main tiling algorithms used in the current public release of PicRead.

## Design Goals
These layout strategies are designed for reviewing images and GIFs rather than for building a generic photo gallery.
The main priorities are:
- preserve the original order
- preserve aspect ratio
- reduce obvious empty space as much as possible
- avoid layouts where a row ends up containing only one image
- remain stable while the window is being resized

## Algorithm 1: Smart Row Partitioning
Algorithm 1 searches around the user-selected row count instead of rigidly splitting everything into equal cells.
It first estimates how many images should fit into each row based on aspect ratios, then evaluates several candidate partitions and chooses the most balanced one.

Its core process is:
1. Convert each image into an aspect ratio.
2. Search several candidate row counts around the target value.
3. Use dynamic programming to divide the ordered image sequence into rows.
4. Score each candidate layout.
5. Choose the layout with fewer empty areas, fewer single-image rows, and better visual balance.

Core snippet:
```python
for candidate_rows in range(min_rows, max_rows + 1):
    dp = [[float("inf")] * (count + 1) for _ in range(candidate_rows + 1)]
    prev = [[-1] * (count + 1) for _ in range(candidate_rows + 1)]
    dp[0][0] = 0.0

    for row in range(1, candidate_rows + 1):
        for end in range(1, count + 1):
            start_floor = row - 1
            start_cap = end - 1
            for start in range(start_floor, start_cap + 1):
                if dp[row - 1][start] == float("inf"):
                    continue
                ratio_sum = prefix_ratio[end] - prefix_ratio[start]
                width_variance = abs(ratio_sum - target_ratio_per_row)
                single_penalty = 0.32 if end - start == 1 and count > candidate_rows else 0.0
                cost = dp[row - 1][start] + width_variance + single_penalty
                if cost < dp[row][end]:
                    dp[row][end] = cost
                    prev[row][end] = start
```

To avoid layouts where images are too small while the bottom of the window still has a lot of empty space, the algorithm also evaluates the layout as a whole:
```python
blank_ratio = max(0.0, total_h - natural_total_h) / max(1.0, total_h)
overflow_ratio = max(0.0, natural_total_h - total_h) / max(1.0, total_h)
fit_penalty = blank_ratio * 4.6 + overflow_ratio * 8.8
fit_penalty += abs(natural_total_h - total_h) / max(1.0, total_h) * 1.8
single_rows_penalty = 0.18 * single_rows
total_cost = candidate_cost * 0.28 + fit_penalty + single_rows_penalty
```

### Best Use Cases
- You want a more stable layout style.
- You still want the row count to have some meaning.
- Image ratios vary a lot, but you do not want the layout to become too aggressive.

## Algorithm 2: Justified-Style Layout
Algorithm 2 is closer to a justified layout that searches across a range of target row heights.
It partitions the ordered sequence into rows and tries to let every row naturally fill the available width.

Core formula:
```python
height = total_w / ratio_sum
```

Meaning:
- every image in the row uses the same row height
- each image width equals `row_height × aspect_ratio`
- the total row width is pushed as close as possible to the available width

Core process:
```python
target_h = min_target_h
while target_h <= max_target_h + 0.1:
    dp = [float("inf")] * (count + 1)
    prev = [-1] * (count + 1)
    row_heights = [0.0] * (count + 1)
    dp[0] = 0.0

    for end in range(1, count + 1):
        start_floor = max(0, end - 8)
        for start in range(start_floor, end):
            ratio_sum = prefix_ratio[end] - prefix_ratio[start]
            height = total_w / ratio_sum
            cost = dp[start]
            cost += ((height - target_h) / max(1.0, target_h)) ** 2
            if end - start == 1 and count > 3:
                cost += 0.45
            if height < 82:
                cost += ((82 - height) / 82) * 2.6
```

The final score also considers:
- bottom empty space
- whether the total layout height overflows
- whether row heights become too short
- whether too many rows contain only one image

Overall scoring snippet:
```python
total_layout_h = sum(heights_out)
blank_ratio = max(0.0, total_h - total_layout_h) / max(1.0, total_h)
overflow_ratio = max(0.0, total_layout_h - total_h) / max(1.0, total_h)
short_penalty = max(0.0, 110.0 - min_height) / 110.0
total_cost = dp[count] * 0.35 + blank_ratio * 3.8 + overflow_ratio * 2.4 + short_penalty * 1.8
```

### Best Use Cases
- You care more about overall space utilization.
- You want to reduce visible empty space on the right side and at the bottom.
- You want mixed horizontal images, vertical images, and GIFs to feel more natural.

## Practical Trade-Offs
As long as the layout must preserve order, preserve aspect ratio, and avoid cropping, empty space can never be reduced to absolute zero in every case.
The goal of these algorithms is not to eliminate all blank areas, but to steer them into a more natural and review-friendly balance.

## Algorithm 3: Review-Size Balanced Layout
Algorithm 3 focuses on review comfort when landscape, portrait, and square images are mixed together.
Instead of forcing every item into rows with the same height, it builds several candidate layouts and chooses the best one with a shared quality score.

The main pain point it addresses is that portrait images can become too narrow and too small when they are forced into the same row height as nearby landscape images.

Core ideas:
1. Preserve the original item order.
2. Generate different candidate rectangles for landscape, portrait, and square images.
3. When a landscape item and a portrait item are adjacent, try grouping them into one review unit so the portrait item can receive more height.
4. Score candidates using short-side readability, area usage, empty space, overflow, and size consistency.
5. Choose the result that best balances screen usage and readable image size.

Landscape/portrait pairing snippet:
```python
if is_landscape and next_portrait:
    portrait_w = min(0.95, max(0.34, next_ratio))
    land_h = portrait_w
    land_w = max(0.35, ratio * land_h)
    unit_w = land_w + portrait_w
    units.append({
        "ratio": unit_w,
        "parts": [
            (idx, 0.0, 0.0, land_w, land_h),
            (idx + 1, land_w, 0.0, unit_w, 1.0),
        ],
    })
```

Candidate layouts are evaluated through a shared score:
```python
slot_mosaic_candidate = self._slot_mosaic_layout_rects(total_w, total_h)
orientation_candidate = self._orientation_mosaic_layout_rects(total_w, total_h)
short_side_candidate = self._short_side_balanced_layout_rects(total_w, total_h)
area_candidate = self._area_balanced_layout_rects(total_w, total_h)

best = max(candidates, key=lambda rects: self._layout_quality_score(rects, total_w, total_h))
```

### Best Use Cases
- Mixed landscape, portrait, and square images
- Portrait images feel too small in Algorithm 1 or Algorithm 2
- Review readability matters more than perfectly uniform row heights
