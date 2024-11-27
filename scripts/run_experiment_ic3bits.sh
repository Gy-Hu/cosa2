#!/bin/bash

# Configuration
BENCHMARK_DIR="/data/guangyuh/coding_env/HWMCC24_benchmark_official/btor2_bv"
RESULTS_FILE="/data/guangyuh/coding_env/ic3ng-fork/build/pono_results_ic3bits.csv"
LOCK_FILE="/tmp/pono_results.lock"
NUM_JOBS=8
TIMEOUT=3600

# Memory limit (in KB) - setting to 3.5GB per process
MEMORY_LIMIT=3500000  # About 3.5GB per process (leaving some memory for system)

# Pono command configuration
PONO_PATH="/data/guangyuh/coding_env/ic3ng-fork/build/pono"
PONO_CMD="$PONO_PATH -e ic3bits --print-wall-time -k 100000"

# Initialize results file if it doesn't exist
init_results_file() {
    if [ ! -f "$RESULTS_FILE" ]; then
        echo "Filename,Result,Wall_Time" > "$RESULTS_FILE"
    fi
}

# Process a single benchmark file
process_file() {
    local file="$1"
    
    # Skip if already processed - check at the start to avoid unnecessary work
    local rel_path=$(realpath --relative-to="$BENCHMARK_DIR" "$file")
    if grep -q "^$rel_path," "$RESULTS_FILE"; then
        echo "Skipping: $file (already processed)"
        return
    fi
    
    # Ensure we're in a valid directory
    cd / || exit 1
    
    echo "Processing: $file"
    
    # Run pono with both timeout and memory limit
    # Using ulimit to restrict memory usage
    local output
    output=$(ulimit -v $MEMORY_LIMIT && timeout "$TIMEOUT" $PONO_CMD "$file" 2>&1)
    local exit_code=$?
    
    # Parse results including memory limit cases
    local result wall_time
    case $exit_code in
        137)  # Timeout cases
            result="timeout"
            wall_time="$TIMEOUT"
            ;;
        0|1)  # Normal completion (0 for 'sat', 1 for 'unsat')
            if echo "$output" | grep -q "^sat"; then
                result="sat"
            elif echo "$output" | grep -q "^unsat"; then
                result="unsat"
            else
                result="unknown"
            fi
            wall_time=$(echo "$output" | grep "wall clock time" | awk '{print $6}')
            ;;
        *)  # Error cases (including memory limit)
            if echo "$output" | grep -q "memory"; then
                result="memout"
            else
                result="unknown"
            fi
            wall_time="0"
            ;;
    esac
    
    # Atomic write to results file
    (
        flock -x 200
        echo "$rel_path,$result,$wall_time" >> "$RESULTS_FILE"
    ) 200>$LOCK_FILE
    
    echo "Completed: $file (Result: $result, Time: $wall_time)"
}

# Print statistics
print_stats() {
    local prefix=$1
    echo "${prefix} results breakdown:"
    echo "SAT cases:     $(grep -c ",sat," "$RESULTS_FILE")"
    echo "UNSAT cases:   $(grep -c ",unsat," "$RESULTS_FILE")"
    echo "UNKNOWN cases: $(grep -c ",unknown," "$RESULTS_FILE")"
    echo "TIMEOUT cases: $(grep -c ",timeout," "$RESULTS_FILE")"
    echo "MEMOUT cases:  $(grep -c ",memout," "$RESULTS_FILE")"
    echo "----------------------------------------"
}

# Progress monitoring function
monitor_progress() {
    while true; do
        sleep 10
        local total=$(find "$BENCHMARK_DIR" -type f -name "*.btor2" | wc -l)
        local completed=$(($(wc -l < "$RESULTS_FILE") - 1))
        local percent=$((completed * 100 / total))
        
        echo "Progress: $completed/$total ($percent%)"
        print_stats "Current"
    done
}

# Main execution
main() {
    init_results_file
    
    # Start progress monitoring
    monitor_progress &
    local monitor_pid=$!
    
    # Setup cleanup on script exit
    trap 'kill $monitor_pid 2>/dev/null; echo "Script interrupted. Results saved in $RESULTS_FILE"; exit' INT TERM
    
    # Process all files in parallel
    export -f process_file
    export BENCHMARK_DIR RESULTS_FILE TIMEOUT LOCK_FILE PONO_CMD MEMORY_LIMIT
    
    find "$BENCHMARK_DIR" -type f -name "*.btor2" | \
        parallel -j "$NUM_JOBS" process_file
    
    # Cleanup and final summary
    kill $monitor_pid 2>/dev/null
    echo "Experiment completed. Results saved in $RESULTS_FILE"
    print_stats "Final"
}

# Run the script
main