import os
import re

def process_lean_files(directory):
    """
    Process all .lean files in the given directory:
    - Extract content before the first ':='
    - Append ' by sorry'
    - Save to a new file with '_targ.lean' suffix
    """
    # Check if the directory exists
    if not os.path.isdir(directory):
        print(f"Error: Directory '{directory}' not found.")
        return
    # Create 'targs' subdirectory if it doesn't exist
    targs_dir = os.path.join(directory, 'targs')
    if not os.path.exists(targs_dir):
        os.makedirs(targs_dir)
        print(f"Created directory: {targs_dir}")
    
    # Count files processed
    processed_count = 0
    
    # Get all .lean files in the directory
    lean_files = [f for f in os.listdir(directory) if f.endswith('.lean')]
    
    for filename in lean_files:
        input_path = os.path.join(directory, filename)
        output_filename = filename.replace('.lean', '_targ.lean')
        output_path = os.path.join(directory, 'targs', output_filename)
        
        try:
            # Read the content of the original file
            with open(input_path, 'r') as file:
                content = file.read()
            
            # Find the position of the first ':='
            assignment_pos = content.find(':=')
            
            if assignment_pos != -1:
                # Extract content before ':=' and append ' by sorry'
                new_content = content[:assignment_pos] + ' := by sorry'
                
                # Write to the new file
                with open(output_path, 'w') as file:
                    file.write(new_content)
                
                processed_count += 1
                print(f"Processed: {filename} -> {output_filename}")
            else:
                print(f"Skipped: {filename} (no ':=' found)")
        
        except Exception as e:
            print(f"Error processing {filename}: {str(e)}")
    
    print(f"\nSummary: Processed {processed_count} out of {len(lean_files)} .lean files.")

if __name__ == "__main__":
    import sys
    
    if len(sys.argv) != 2:
        print("Usage: python script_name.py <directory_path>")
    else:
        directory = sys.argv[1]
        process_lean_files(directory)

