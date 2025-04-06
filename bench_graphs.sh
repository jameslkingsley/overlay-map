#!/usr/bin/env bash

set -e

echo "🔧 Running Criterion benchmarks..."
cargo bench --bench compare

echo "📁 Ensuring assets directory exists..."
mkdir -p ./assets

# Define source paths
OVERLAY_DIR=target/criterion/push/overlay/report
TUPLE_DIR=target/criterion/push/tuple/report

# Define destination paths
cp "$OVERLAY_DIR/regression_small.svg" ./assets/overlay_regression.svg
cp "$OVERLAY_DIR/pdf_small.svg"        ./assets/overlay_pdf.svg

cp "$TUPLE_DIR/regression_small.svg"   ./assets/tuple_regression.svg
cp "$TUPLE_DIR/pdf_small.svg"          ./assets/tuple_pdf.svg

echo "✅ SVGs copied to ./assets/"
