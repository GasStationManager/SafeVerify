import os
import subprocess
import json

def compile(fname):
    """
    Compile a Lean file and return success status and output
    """
    assert fname.endswith('.lean')
    ofname = fname[:-5] + '.olean'
    result = subprocess.run(["lake", "env", "lean", '-o', ofname, fname], capture_output=True, text=True)
    # Check if Lean 4 succeeded (return code 0 means success)
    is_correct = result.returncode == 0
    
    # Also verify the output file actually exists
    if is_correct and not os.path.exists(ofname):
        is_correct = False
        result_output = result.stderr + result.stdout
        result_output += f"\nError: Output file '{ofname}' was not created."
        return is_correct, result_output
    
    return is_correct, result.stderr + result.stdout

def safe_verify(otarg, osub):
    """
    Run safe_verify on two olean files
    """
    # First check if both files exist
    for f in [otarg, osub]:
        if not os.path.exists(f):
            return False, f"Error: File '{f}' does not exist."
    
    result = subprocess.run(["lake", "env", "safe_verify", otarg, osub], capture_output=True, text=True)
    is_correct = result.returncode == 0
    return is_correct, result.stderr + result.stdout

def process_lean_directory(directory):
    """
    Process all .lean files in the given directory by compiling and verifying them
    """
    # Check if the directory exists
    if not os.path.isdir(directory):
        print(f"Error: Directory '{directory}' not found.")
        return
    
    # Make sure targs directory exists
    targs_dir = os.path.join(directory, 'targs')
    if not os.path.exists(targs_dir):
        print(f"Error: 'targs' directory not found at {targs_dir}.")
        print("Make sure to run the first script to create the target files.")
        return
    
    # Create error log file
    error_log_path = os.path.join(directory, 'verification_errors.jsonl')
    
    # Count files processed
    processed_count = 0
    error_count = 0
    
    # Track compiled files to avoid duplicate compilation
    compiled_files = set()
    
    # Get all .lean files in the directory
    lean_files = [f for f in os.listdir(directory) if f.endswith('.lean')]
    
    print(f"Found {len(lean_files)} .lean files to process.")
    
    for filename in lean_files:
        print(f"\nProcessing {filename}...")
        
        # Define paths
        original_path = os.path.join(directory, filename)
        targ_filename = filename.replace('.lean', '_targ.lean')
        targ_path = os.path.join(directory, 'targs', targ_filename)
        
        # Check if target file exists
        if not os.path.exists(targ_path):
            print(f"Skipping {filename}: Target file {targ_filename} not found in targs/ directory.")
            continue
            
        # Define output paths
        original_olean = original_path.replace('.lean', '.olean')
        targ_olean = targ_path.replace('.lean', '.olean')
        
        try:
            # Compile original file if not already compiled
            if original_path not in compiled_files:
                print(f"Compiling {filename}...")
                success, output = compile(original_path)
                compiled_files.add(original_path)
                
                if not success:
                    print(f"Error compiling {filename}:")
                    print(output[:200] + "..." if len(output) > 200 else output)
                    
                    # Log error
                    error_data = {
                        "file": filename,
                        "stage": "compile_original",
                        "error": output
                    }
                    with open(error_log_path, 'a') as error_file:
                        error_file.write(json.dumps(error_data) + '\n')
                        
                    error_count += 1
                    continue
            else:
                print(f"Skipping compilation for {filename} (already compiled)")
            
            # Ensure the targs directory exists again inside each file's directory path
            targ_dir = os.path.dirname(targ_path)
            if not os.path.exists(targ_dir):
                os.makedirs(targ_dir)
                print(f"Created directory: {targ_dir}")
                
            # Compile target file if not already compiled
            if targ_path not in compiled_files:
                print(f"Compiling {targ_filename}...")
                success, output = compile(targ_path)
                compiled_files.add(targ_path)
                
                if not success:
                    print(f"Error compiling {targ_filename}:")
                    print(output[:200] + "..." if len(output) > 200 else output)
                    
                    # Log error
                    error_data = {
                        "file": filename,
                        "stage": "compile_target",
                        "error": output
                    }
                    with open(error_log_path, 'a') as error_file:
                        error_file.write(json.dumps(error_data) + '\n')
                        
                    error_count += 1
                    continue
            else:
                print(f"Skipping compilation for {targ_filename} (already compiled)")
                
            # Check if both olean files exist before verification
            if not os.path.exists(original_olean):
                error_msg = f"Error: Original olean file '{original_olean}' does not exist after compilation."
                print(error_msg)
                error_data = {
                    "file": filename,
                    "stage": "verification_prep",
                    "error": error_msg
                }
                with open(error_log_path, 'a') as error_file:
                    error_file.write(json.dumps(error_data) + '\n')
                error_count += 1
                continue
                
            if not os.path.exists(targ_olean):
                error_msg = f"Error: Target olean file '{targ_olean}' does not exist after compilation."
                print(error_msg)
                error_data = {
                    "file": filename,
                    "stage": "verification_prep",
                    "error": error_msg
                }
                with open(error_log_path, 'a') as error_file:
                    error_file.write(json.dumps(error_data) + '\n')
                error_count += 1
                continue
            
            # Run safe_verify
            print(f"Verifying {filename} against {targ_filename}...")
            success, output = safe_verify(targ_olean, original_olean)
            if not success:
                print(f"Verification failed for {filename}:")
                print(output[:200] + "..." if len(output) > 200 else output)
                
                # Log error
                error_data = {
                    "file": filename,
                    "stage": "verification",
                    "error": output
                }
                with open(error_log_path, 'a') as error_file:
                    error_file.write(json.dumps(error_data) + '\n')
                    
                error_count += 1
            else:
                print(f"Successfully verified {filename}!")
                
            processed_count += 1
            
        except Exception as e:
            print(f"Error processing {filename}: {str(e)}")
            
            # Log error
            error_data = {
                "file": filename,
                "stage": "exception",
                "error": str(e)
            }
            with open(error_log_path, 'a') as error_file:
                error_file.write(json.dumps(error_data) + '\n')
                
            error_count += 1
    
    print(f"\nSummary: Processed {processed_count} out of {len(lean_files)} .lean files.")
    print(f"Encountered {error_count} errors. Check {error_log_path} for details.")

if __name__ == "__main__":
    import sys
    
    if len(sys.argv) != 2:
        print("Usage: python script_name.py <directory_path>")
    else:
        directory = sys.argv[1]
        process_lean_directory(directory)

