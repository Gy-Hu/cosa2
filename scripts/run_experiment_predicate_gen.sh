#!/usr/bin/env zsh

# Directory containing BTOR2 files
BTOR_DIR="/data/guangyuh/coding_env/ic3ng-fork/samples/hwmcc_btor2_bv"

# Log file
LOG_FILE="generate_predicates.log"

# Initialize conda
echo "Initializing conda environment..." | tee -a "$LOG_FILE"
source ~/miniconda3/bin/activate || {
    echo "Failed to initialize conda" | tee -a "$LOG_FILE"
    exit 1
}

# Activate specific environment if needed
# Uncomment and modify if you have a specific conda environment
# conda activate your_env_name || {
#     echo "Failed to activate conda environment" | tee -a "$LOG_FILE"
#     exit 1
# }

# Verify Python environment
echo "Using Python: $(which python)" | tee -a "$LOG_FILE"
echo "Python version: $(python --version)" | tee -a "$LOG_FILE"

echo "Starting predicate generation at $(date)" | tee -a "$LOG_FILE"

# Counter for progress tracking
total_files=$(find "$BTOR_DIR" -name "*.btor2" | wc -l)
current=0

for f in "$BTOR_DIR"/**/*.btor2; do
    ((current++))
    
    # Get base name without extension
    base_name="${f%.btor2}"
    
    # Check for any .smt2 files with this base name
    if ls "${base_name}"*.smt2 1> /dev/null 2>&1; then
        echo "[${current}/${total_files}] Skipping $f (found existing .smt2 file)" | tee -a "$LOG_FILE"
        echo "----------------------------------------" | tee -a "$LOG_FILE"
        continue
    fi
    
    echo "[${current}/${total_files}] Processing $f..." | tee -a "$LOG_FILE"
    if python generate_predicates.py "$f" --verbose --validate; then
        echo "✓ Success: $f" | tee -a "$LOG_FILE"
    else
        echo "✗ Failed: $f" | tee -a "$LOG_FILE"
    fi
    echo "----------------------------------------" | tee -a "$LOG_FILE"
done

echo "Completed predicate generation at $(date)" | tee -a "$LOG_FILE"