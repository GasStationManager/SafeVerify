#!/bin/bash
# SafeVerify Test Runner
# This script compiles test cases and runs SafeVerify on them,
# verifying that "Good" submissions pass and "Bad" submissions fail.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TEST_DIR="$PROJECT_ROOT/SafeVerifyTest"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

PASSED=0
FAILED=0
SKIPPED=0
SETUP_FAILED=0

# Function to compile a lean file to olean
compile_lean() {
    local lean_file="$1"
    local olean_file="${lean_file%.lean}.olean"
    
    echo "  Compiling $lean_file..."
    if lake env lean -o "$olean_file" "$lean_file" 2>/dev/null; then
        echo "  Compiled successfully to $olean_file"
        return 0
    else
        echo "  Failed to compile $lean_file"
        return 1
    fi
}

# Function to run SafeVerify and check expected outcome
run_test() {
    local test_name="$1"
    local target_olean="$2"
    local submission_olean="$3"
    local expected_result="$4"  # "pass" or "fail"
    
    echo "Running test: $test_name (expecting: $expected_result)"
    
    if lake exe safe_verify "$target_olean" "$submission_olean" >/dev/null 2>&1; then
        actual_result="pass"
    else
        actual_result="fail"
    fi
    
    if [ "$actual_result" = "$expected_result" ]; then
        echo -e "  ${GREEN}✓ PASSED${NC}: SafeVerify $actual_result as expected"
        PASSED=$((PASSED + 1))
        return 0
    else
        echo -e "  ${RED}✗ FAILED${NC}: SafeVerify $actual_result but expected $expected_result"
        FAILED=$((FAILED + 1))
        return 1
    fi
}

# Cleanup function to remove generated olean files
cleanup() {
    echo "Cleaning up generated olean files..."
    find "$TEST_DIR" -name "*.olean" -type f -delete 2>/dev/null || true
    find "$TEST_DIR" -name "*.ilean" -type f -delete 2>/dev/null || true
    find "$TEST_DIR" -name "*.trace" -type f -delete 2>/dev/null || true
}

# Main test execution
main() {
    echo "========================================="
    echo "SafeVerify Test Suite"
    echo "========================================="
    echo ""
    
    cd "$PROJECT_ROOT"
    
    # Make sure SafeVerify is built
    echo "Building SafeVerify..."
    lake build safe_verify
    echo ""
    
    # Clean up any previous test artifacts
    cleanup
    echo ""
    
    # Iterate through test directories
    for test_dir in "$TEST_DIR"/*/; do
        test_name=$(basename "$test_dir")
        target_file="$test_dir/Target.lean"
        
        if [ ! -f "$target_file" ]; then
            echo -e "${YELLOW}Skipping $test_name: No Target.lean found${NC}"
            SKIPPED=$((SKIPPED + 1))
            continue
        fi
        
        echo "========================================="
        echo "Test Case: $test_name"
        echo "========================================="
        
        # Compile Target.lean
        target_olean="${target_file%.lean}.olean"
        if ! compile_lean "$target_file"; then
            echo -e "${RED}Failed to compile Target.lean for $test_name${NC}"
            SETUP_FAILED=1
            continue
        fi
        
        # Process Good.lean files (should pass)
        if [ -f "$test_dir/Good.lean" ]; then
            good_file="$test_dir/Good.lean"
            good_olean="${good_file%.lean}.olean"
            if compile_lean "$good_file"; then
                run_test "$test_name/Good" "$target_olean" "$good_olean" "pass" || true
            else
                echo -e "${RED}Failed to compile Good.lean for $test_name${NC}"
                SETUP_FAILED=1
            fi
        fi
        
        # Process Bad.lean files (should fail)
        if [ -f "$test_dir/Bad.lean" ]; then
            bad_file="$test_dir/Bad.lean"
            bad_olean="${bad_file%.lean}.olean"
            if compile_lean "$bad_file"; then
                run_test "$test_name/Bad" "$target_olean" "$bad_olean" "fail" || true
            else
                # Bad.lean files might intentionally fail to compile
                # This is actually expected for some exploit attempts
                echo -e "${YELLOW}Note: Bad.lean for $test_name failed to compile (this may be expected)${NC}"
                SKIPPED=$((SKIPPED + 1))
            fi
        fi
        
        # Process Maybe.lean files (skip - undefined behavior)
        if [ -f "$test_dir/Maybe.lean" ]; then
            echo -e "${YELLOW}Skipping Maybe.lean for $test_name (undefined expected behavior)${NC}"
            SKIPPED=$((SKIPPED + 1))
        fi
        
        echo ""
    done
    
    # Cleanup
    cleanup
    
    # Summary
    echo "========================================="
    echo "Test Summary"
    echo "========================================="
    echo -e "Passed:  ${GREEN}$PASSED${NC}"
    echo -e "Failed:  ${RED}$FAILED${NC}"
    echo -e "Skipped: ${YELLOW}$SKIPPED${NC}"
    echo ""
    
    if [ $FAILED -gt 0 ]; then
        echo -e "${RED}Some tests failed!${NC}"
        exit 1
    elif [ $SETUP_FAILED -gt 0 ]; then
        echo -e "${RED}Some test setups failed!${NC}"
        exit 1
    else
        echo -e "${GREEN}All tests passed!${NC}"
        exit 0
    fi
}

# Run main function
main "$@"
