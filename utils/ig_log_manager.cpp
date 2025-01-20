#include "utils/ig_log_manager.h"
#include <iostream>
#include <zlib.h>

namespace pono {

IGLogManager::IGLogManager(const PonoOptions & opts, const std::string & base_path)
  : opts_(opts),
    base_path_(base_path),
    current_size_(0),
    chunk_count_(0),
    compress_enabled_(opts.ig_data_compress_) {
  // Create base directory if it doesn't exist
  std::filesystem::create_directories(base_path_);
  create_new_chunk();
}

IGLogManager::~IGLogManager() {
  flush();
  if (current_file_.is_open()) {
    current_file_.close();
    if (compress_enabled_) {
      compress_file(current_chunk_path_);
    }
  }
}

void IGLogManager::log_data(const nlohmann::ordered_json & data) {
  // Add data to buffer
  buffer_.push_back(data);

  // Estimate size (approximate)
  current_size_ += data.dump().size();

  // Check if we need to flush based on buffer size or chunk size
  if (buffer_.size() >= BUFFER_SIZE || 
      current_size_ >= opts_.ig_data_chunk_size_ * BYTES_PER_MB) {
    flush();
  }
}

void IGLogManager::flush() {
  if (buffer_.empty()) {
    return;
  }

  // Write all buffered data
  for (const auto & entry : buffer_) {
    current_file_ << entry.dump(2) << "\n";
  }
  current_file_.flush();

  // Clear buffer
  buffer_.clear();

  // Check if we need to start a new chunk
  if (current_size_ >= opts_.ig_data_chunk_size_ * BYTES_PER_MB) {
    current_file_.close();
    if (compress_enabled_) {
      compress_file(current_chunk_path_);
    }
    create_new_chunk();
  }
}

void IGLogManager::create_new_chunk() {
  // Generate new chunk file name
  current_chunk_path_ = base_path_ + "/chunk_" + 
                       std::to_string(chunk_count_++) + ".json";
  
  // Open new file
  current_file_.open(current_chunk_path_);
  if (!current_file_) {
    throw std::runtime_error("Failed to create log chunk file: " + current_chunk_path_);
  }
  
  current_size_ = 0;
}

void IGLogManager::compress_file(const std::string & file_path) {
  std::string gz_path = file_path + ".gz";
  
  // Open input file
  std::ifstream in(file_path, std::ios::binary);
  if (!in) {
    std::cerr << "Warning: Could not open file for compression: " << file_path << std::endl;
    return;
  }

  // Open output file
  gzFile out = gzopen(gz_path.c_str(), "wb");
  if (!out) {
    std::cerr << "Warning: Could not create compressed file: " << gz_path << std::endl;
    return;
  }

  // Compress file
  char buf[8192];
  while (in) {
    in.read(buf, sizeof(buf));
    int bytes_read = in.gcount();
    if (bytes_read > 0) {
      int bytes_written = gzwrite(out, buf, bytes_read);
      if (bytes_written != bytes_read) {
        std::cerr << "Warning: Failed to compress data" << std::endl;
        break;
      }
    }
  }

  // Clean up
  gzclose(out);
  in.close();

  // Remove original file
  std::filesystem::remove(file_path);
}

} // namespace pono
