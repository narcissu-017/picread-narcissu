# 排版算法说明

本文档说明 PicRead 当前公开版本里使用的两种主要平铺算法。

## 设计目标
这套排版逻辑主要服务于图片与 GIF 审阅，而不是普通相册展示。
它优先满足这些目标：
- 保持原始顺序
- 保持宽高比
- 尽量减少明显空白
- 尽量避免某一行只剩一张图
- 在窗口缩放时仍保持稳定

## 算法 1：智能分行排版
算法 1 会围绕用户设置的“行数”做一轮有限搜索。它不会死板地把所有内容均分成固定格子，而是先按宽高比估算每一行应该容纳哪些图片，再从多个候选分法里选出更合理的一种。

它的核心过程是：
1. 先把每张图片转成宽高比。
2. 在目标行数附近搜索候选行数。
3. 用动态规划把顺序不变的图片分成多行。
4. 对每种分法做评分。
5. 选出空白更少、单图行更少、视觉更均衡的布局。

核心片段：
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

为了避免“图片很小但底部还空很多”或“整体被压得太扁”，算法还会对最终布局再做一次整体评分：
```python
blank_ratio = max(0.0, total_h - natural_total_h) / max(1.0, total_h)
overflow_ratio = max(0.0, natural_total_h - total_h) / max(1.0, total_h)
fit_penalty = blank_ratio * 4.6 + overflow_ratio * 8.8
fit_penalty += abs(natural_total_h - total_h) / max(1.0, total_h) * 1.8
single_rows_penalty = 0.18 * single_rows
total_cost = candidate_cost * 0.28 + fit_penalty + single_rows_penalty
```

### 适合场景
- 想让排版更稳定
- 仍然希望“行数”有一定参考意义
- 图片比例差异较大，但不希望布局变化太激进

## 算法 2：Justified 风格排版
算法 2 更接近“按目标行高搜索”的 justified layout。它会尝试一批目标行高，把顺序不变的图片划分成多行，并尽量让每一行自然铺满宽度。

核心公式：
```python
height = total_w / ratio_sum
```

含义是：
- 同一行里每张图的宽度都等于 `行高 × 宽高比`
- 所有图片宽度加起来应尽量接近整行宽度
- 这样可以自然得到一行的合理高度

核心过程：
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

最终会综合考虑：
- 底部空白
- 总高度是否溢出
- 行高是否过矮
- 单图行是否过多

整体评分片段：
```python
total_layout_h = sum(heights_out)
blank_ratio = max(0.0, total_h - total_layout_h) / max(1.0, total_h)
overflow_ratio = max(0.0, total_layout_h - total_h) / max(1.0, total_h)
short_penalty = max(0.0, 110.0 - min_height) / 110.0
total_cost = dp[count] * 0.35 + blank_ratio * 3.8 + overflow_ratio * 2.4 + short_penalty * 1.8
```

### 适合场景
- 更看重整体利用率
- 更在意减少右侧和底部空白
- 想让横图、竖图、GIF 混排时更自然

## 实际取舍
在保持顺序、比例、不裁切的前提下，空白不可能永远完全为零。
这两套算法的意义不是“消灭全部空白”，而是把空白控制在更自然、更适合审阅的方向。
