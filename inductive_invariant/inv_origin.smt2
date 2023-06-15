(define-fun assumption.0 ((mem_do_wdata (_ BitVec 1)) (latched_rd (_ BitVec 5)) (mem_do_rdata (_ BitVec 1)) (mem_do_rinst (_ BitVec 1)) (latched_compr (_ BitVec 1)) (mem_valid (_ BitVec 1)) (trap (_ BitVec 1)) (latched_branch (_ BitVec 1)) (instr_jal (_ BitVec 1)) (decoded_rd (_ BitVec 5)) (cpu_state (_ BitVec 8)) (instr_jalr (_ BitVec 1)) (mem_do_prefetch (_ BitVec 1)) (decoder_trigger (_ BitVec 1))) Bool (and (and (and (and (and (and (and (and true (or (not (= ((_ extract 0 0) mem_do_rinst) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 0 0) decoder_trigger) ((_ extract 0 0) (_ bv1 1)))))) (or (not (= ((_ extract 0 0) trap) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 7 7) cpu_state) ((_ extract 7 7) (_ bv8 8)))))) (or (or (not (= ((_ extract 7 7) cpu_state) ((_ extract 7 7) (_ bv32 8)))) (not (= ((_ extract 0 0) instr_jalr) ((_ extract 0 0) (_ bv1 1))))) (not (= ((_ extract 0 0) mem_do_prefetch) ((_ extract 0 0) (_ bv1 1)))))) (or (not (= ((_ extract 0 0) latched_branch) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 0 0) cpu_state) ((_ extract 0 0) (_ bv1 8)))))) (or (not (= ((_ extract 0 0) latched_branch) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 5 5) cpu_state) ((_ extract 5 5) (_ bv32 8)))))) (or (or (or (not (= ((_ extract 0 0) latched_rd) ((_ extract 0 0) (_ bv17 5)))) (not (= ((_ extract 0 0) mem_do_rinst) ((_ extract 0 0) (_ bv1 1))))) (not (= ((_ extract 0 0) instr_jalr) ((_ extract 0 0) (_ bv1 1))))) (not (= ((_ extract 3 3) cpu_state) ((_ extract 3 3) (_ bv8 8)))))) (or (or (or (not (= ((_ extract 7 7) cpu_state) ((_ extract 7 7) (_ bv2 8)))) (not (= ((_ extract 6 6) cpu_state) ((_ extract 6 6) (_ bv2 8))))) (not (= ((_ extract 4 4) latched_rd) ((_ extract 4 4) (_ bv17 5))))) (not (= ((_ extract 0 0) latched_branch) ((_ extract 0 0) (_ bv1 1)))))) (not (and (and (and (and (and (and (and (and (and (and (= cpu_state (_ bv64 8)) (and (= ((_ extract 1 0) decoded_rd) ((_ extract 1 0) (_ bv15 5))) (= ((_ extract 4 4) decoded_rd) ((_ extract 4 4) (_ bv15 5))))) (= decoder_trigger (_ bv1 1))) (= instr_jal (_ bv1 1))) (= latched_branch (_ bv1 1))) (= latched_compr (_ bv0 1))) (= latched_rd (_ bv17 5))) (= mem_do_rdata (_ bv0 1))) (= mem_do_rinst (_ bv0 1))) (= mem_do_wdata (_ bv0 1))) (= mem_valid (_ bv0 1))))))
(define-fun assumption.1 ((mem_valid (_ BitVec 1)) (decoder_trigger (_ BitVec 1)) (mem_instr (_ BitVec 1)) (mem_do_wdata (_ BitVec 1)) (mem_do_rinst (_ BitVec 1)) (mem_do_rdata (_ BitVec 1)) (latched_store (_ BitVec 1)) (latched_stalu (_ BitVec 1)) (mem_state (_ BitVec 2)) (latched_branch (_ BitVec 1)) (instr_jal (_ BitVec 1)) (compressed_instr (_ BitVec 1))) Bool (and (and true (or (or (not (= ((_ extract 0 0) mem_valid) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 1 1) mem_state) ((_ extract 1 1) (_ bv3 2))))) (not (= ((_ extract 0 0) mem_state) ((_ extract 0 0) (_ bv3 2)))))) (not (and (and (and (and (and (and (and (and (and (and (= compressed_instr (_ bv0 1)) (= decoder_trigger (_ bv1 1))) (= instr_jal (_ bv1 1))) (= latched_branch (_ bv0 1))) (= latched_stalu (_ bv0 1))) (= latched_store (_ bv1 1))) (= mem_do_rdata (_ bv0 1))) (= mem_do_rinst (_ bv0 1))) (= mem_do_wdata (_ bv0 1))) (= mem_instr (_ bv1 1))) (= mem_valid (_ bv1 1))))))
(define-fun assumption.2 ((mem_valid (_ BitVec 1)) (mem_do_wdata (_ BitVec 1)) (mem_do_rinst (_ BitVec 1)) (latched_store (_ BitVec 1)) (latched_stalu (_ BitVec 1)) (latched_branch (_ BitVec 1)) (decoder_trigger (_ BitVec 1)) (instr_jal (_ BitVec 1)) (cpu_state (_ BitVec 8)) (compressed_instr (_ BitVec 1))) Bool (and (and (and (and true (not (= ((_ extract 4 4) cpu_state) ((_ extract 4 4) (_ bv16 8))))) (or (not (= ((_ extract 0 0) latched_branch) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 5 5) cpu_state) ((_ extract 5 5) (_ bv32 8)))))) (or (not (= ((_ extract 0 0) latched_branch) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 1 1) cpu_state) ((_ extract 1 1) (_ bv2 8)))))) (not (and (and (and (and (and (and (and (and (= compressed_instr (_ bv0 1)) (= decoder_trigger (_ bv1 1))) (= instr_jal (_ bv1 1))) (= latched_branch (_ bv1 1))) (= latched_stalu (_ bv1 1))) (= latched_store (_ bv1 1))) (= mem_do_rinst (_ bv0 1))) (= mem_do_wdata (_ bv1 1))) (= mem_valid (_ bv0 1))))))
(define-fun assumption.3 ((mem_valid (_ BitVec 1)) (mem_do_rinst (_ BitVec 1)) (latched_branch (_ BitVec 1)) (mem_do_rdata (_ BitVec 1)) (latched_store (_ BitVec 1)) (latched_stalu (_ BitVec 1)) (instr_jal (_ BitVec 1)) (decoder_trigger (_ BitVec 1)) (compressed_instr (_ BitVec 1))) Bool (and (and true (or (not (= ((_ extract 0 0) compressed_instr) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 0 0) instr_jal) ((_ extract 0 0) (_ bv1 1)))))) (not (and (and (and (and (and (and (and (and (= compressed_instr (_ bv1 1)) (= decoder_trigger (_ bv1 1))) (= instr_jal (_ bv1 1))) (= latched_branch (_ bv0 1))) (= latched_stalu (_ bv0 1))) (= latched_store (_ bv1 1))) (= mem_do_rdata (_ bv1 1))) (= mem_do_rinst (_ bv0 1))) (= mem_valid (_ bv0 1))))))
(define-fun assumption.4 ((mem_valid (_ BitVec 1)) (mem_do_wdata (_ BitVec 1)) (latched_store (_ BitVec 1)) (mem_do_rinst (_ BitVec 1)) (trap (_ BitVec 1)) (latched_stalu (_ BitVec 1)) (latched_branch (_ BitVec 1)) (instr_jal (_ BitVec 1)) (decoder_trigger (_ BitVec 1)) (compressed_instr (_ BitVec 1)) (cpu_state (_ BitVec 8))) Bool (and (and (and (and (and true (or (not (= ((_ extract 7 7) cpu_state) ((_ extract 7 7) (_ bv2 8)))) (not (= ((_ extract 0 0) trap) ((_ extract 0 0) (_ bv1 1)))))) (not (= ((_ extract 4 4) cpu_state) ((_ extract 4 4) (_ bv16 8))))) (or (not (= ((_ extract 0 0) latched_store) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 5 5) cpu_state) ((_ extract 5 5) (_ bv32 8)))))) (or (not (= ((_ extract 0 0) latched_store) ((_ extract 0 0) (_ bv1 1)))) (not (= ((_ extract 1 1) cpu_state) ((_ extract 1 1) (_ bv2 8)))))) (not (and (and (and (and (and (and (and (and (= compressed_instr (_ bv0 1)) (= decoder_trigger (_ bv1 1))) (= instr_jal (_ bv1 1))) (= latched_branch (_ bv0 1))) (= latched_stalu (_ bv1 1))) (= latched_store (_ bv1 1))) (= mem_do_rinst (_ bv0 1))) (= mem_do_wdata (_ bv1 1))) (= mem_valid (_ bv0 1))))))
