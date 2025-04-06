#!/usr/bin/env bash

set -e

echo "🔧 Running Criterion benchmarks..."
cargo bench --bench compare

echo "📁 Ensuring assets directory exists..."
mkdir -p ./assets

# Define source paths
OVERLAY_DIR="target/criterion/push/overlay/report"
TUPLE_DIR="target/criterion/push/tuple/report"

# Define destination paths
cp "$OVERLAY_DIR/regression_small.svg" ./assets/overlay_regression.svg
cp "$OVERLAY_DIR/pdf_small.svg"        ./assets/overlay_pdf.svg
cp "$TUPLE_DIR/regression_small.svg"   ./assets/tuple_regression.svg
cp "$TUPLE_DIR/pdf_small.svg"          ./assets/tuple_pdf.svg

# Patch SVGs for dark mode compatibility
for svg in ./assets/*.svg; do
    echo "🎨 Patching $svg for dark mode compatibility..."

    sed -i '' \
      -e "s/fill=['\"]black['\"]/fill=\"currentColor\"/g" \
      -e "s/stroke=['\"]black['\"]/stroke=\"currentColor\"/g" \
      -e "s/color=['\"]black['\"]/color=\"currentColor\"/g" \
      "$svg"
done

echo "✅ All SVGs copied and patched in ./assets/"
