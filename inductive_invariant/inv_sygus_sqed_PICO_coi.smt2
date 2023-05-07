(define-fun assumption.0 ((RTL.cpu_state (_ BitVec 8)) (RTL.mem_wordsize (_ BitVec 2)) (RTL.instr_jal (_ BitVec 1)) (RTL.mem_valid (_ BitVec 1)) (RTL.is_alu_reg_imm (_ BitVec 1)) (RTL.mem_instr (_ BitVec 1)) (RTL.decoded_rd (_ BitVec 5)) (RTL.latched_rd (_ BitVec 5)) (RTL.is_jalr_addi_slti_sltiu_xori_ori_andi (_ BitVec 1)) (RTL.mem_state (_ BitVec 2)) (RTL.decoder_trigger_q (_ BitVec 1)) (RTL.instr_retirq (_ BitVec 1)) (RTL.latched_store (_ BitVec 1)) (RTL.mem_do_rinst (_ BitVec 1)) (RTL.rvfi_trap (_ BitVec 1)) (RTL.latched_branch (_ BitVec 1))) Bool (and true (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= RTL.mem_valid (_ bv1 1)) (= RTL.is_alu_reg_imm (_ bv1 1))) (= RTL.mem_instr (_ bv1 1))) (= RTL.cpu_state (_ bv64 8))) (= RTL.latched_store (_ bv0 1))) (= RTL.mem_wordsize (_ bv3 2))) (= RTL.instr_jal (_ bv0 1))) (= RTL.latched_branch (_ bv0 1))) (= RTL.rvfi_trap (_ bv0 1))) (= RTL.mem_do_rinst (_ bv1 1))) (= RTL.instr_retirq (_ bv0 1))) (= RTL.decoder_trigger_q (_ bv0 1))) (= RTL.mem_state (_ bv3 2))) (= RTL.is_jalr_addi_slti_sltiu_xori_ori_andi (_ bv1 1))) (= RTL.latched_rd (_ bv31 5))) (= RTL.decoded_rd (_ bv0 5))))))
(define-fun assumption.1 ((RTL.instr_rdinstr (_ BitVec 1)) (RTL.instr_rdcycleh (_ BitVec 1)) (RTL.instr_rdcycle (_ BitVec 1)) (RTL.instr_rdinstrh (_ BitVec 1)) (RTL.instr_lbu (_ BitVec 1)) (RTL.instr_lw (_ BitVec 1)) (RTL.mem_do_wdata (_ BitVec 1)) (RTL.mem_rdata_q (_ BitVec 32)) (RTL.instr_blt (_ BitVec 1)) (RTL.decoder_trigger (_ BitVec 1)) (RTL.do_waitirq (_ BitVec 1)) (RTL.trap (_ BitVec 1)) (RTL.mem_do_rinst (_ BitVec 1)) (RTL.instr_slti (_ BitVec 1)) (RTL.rvfi_trap (_ BitVec 1)) (RTL.mem_state (_ BitVec 2)) (RTL.decoder_trigger_q (_ BitVec 1)) (RTL.is_jalr_addi_slti_sltiu_xori_ori_andi (_ BitVec 1)) (RTL.instr_srl (_ BitVec 1)) (RTL.instr_bge (_ BitVec 1)) (RTL.instr_add (_ BitVec 1)) (RTL.instr_jal (_ BitVec 1)) (RTL.instr_slli (_ BitVec 1)) (RTL.instr_sll (_ BitVec 1)) (RTL.instr_and (_ BitVec 1)) (RTL.mem_do_prefetch (_ BitVec 1)) (RTL.mem_instr (_ BitVec 1)) (RTL.instr_lh (_ BitVec 1)) (RTL.mem_wordsize (_ BitVec 2)) (RTL.decoder_pseudo_trigger (_ BitVec 1)) (RTL.instr_lb (_ BitVec 1)) (RTL.instr_srai (_ BitVec 1)) (RTL.cpu_state (_ BitVec 8)) (RTL.is_beq_bne_blt_bge_bltu_bgeu (_ BitVec 1)) (RTL.decoded_rd (_ BitVec 5)) (RTL.instr_srli (_ BitVec 1)) (RTL.instr_sra (_ BitVec 1)) (RTL.mem_do_rdata (_ BitVec 1)) (RTL.instr_jalr (_ BitVec 1)) (RTL.instr_slt (_ BitVec 1)) (RTL.mem_valid (_ BitVec 1)) (RTL.instr_retirq (_ BitVec 1)) (RTL.instr_lhu (_ BitVec 1)) (RTL.latched_store (_ BitVec 1)) (RTL.is_alu_reg_imm (_ BitVec 1)) (RTL.latched_branch (_ BitVec 1)) (RTL.instr_bne (_ BitVec 1))) Bool (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (or (or (or (= (_ bv1 1) RTL.latched_store) (not (= (_ bv1 1) RTL.mem_do_rdata))) (not (= RTL.latched_branch RTL.latched_store))) (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (not (= (_ bv1 1) (bvcomp RTL.mem_wordsize (_ bv2 2)))))) (or (or (or (or (= (_ bv1 1) RTL.latched_store) (not (= (_ bv1 1) RTL.mem_do_rdata))) (not (= RTL.latched_branch RTL.latched_store))) (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (not (= (bvcomp RTL.mem_wordsize (_ bv2 2)) (ite (not (distinct RTL.mem_wordsize (_ bv0 2))) (_ bv1 1) (_ bv0 1)))))) (not (= (_ bv1 1) RTL.do_waitirq))) (or (not (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 4) (_ bv8 4))))) (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) RTL.decoder_pseudo_trigger))) (or (or (not (= (_ bv1 1) RTL.is_beq_bne_blt_bge_bltu_bgeu)) (not (= (_ bv1 1) (bvand RTL.decoder_trigger (bvnot RTL.decoder_pseudo_trigger))))) (not (= (_ bv1 1) (bvand RTL.is_alu_reg_imm (bvcomp ((_ extract 14 12) RTL.mem_rdata_q) (_ bv5 3))))))) (or (or (or (not (= (_ bv1 1) RTL.decoder_trigger)) (not (= (_ bv1 1) RTL.is_alu_reg_imm))) (not (= (_ bv1 1) RTL.is_beq_bne_blt_bge_bltu_bgeu))) (= (_ bv1 1) RTL.decoder_pseudo_trigger))) (not (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 3) (_ bv16 5)))))) (or (or (or (or (or (or (= (_ bv1 1) RTL.latched_store) (not (= (_ bv1 1) RTL.mem_valid))) (= (_ bv1 1) RTL.decoder_trigger)) (not (= (_ bv1 1) RTL.is_alu_reg_imm))) (not (= RTL.latched_branch RTL.latched_store))) (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvor RTL.decoder_trigger RTL.do_waitirq)))) (or (or (or (or (or (or (not (= (_ bv1 1) RTL.mem_valid)) (not (= (_ bv1 1) (bvor RTL.mem_do_rinst RTL.mem_do_rdata)))) (not (= (_ bv3 2) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state)))) (= (_ bv1 1) (bvcomp RTL.mem_wordsize ((_ zero_extend 1) (_ bv1 1))))) (= RTL.is_alu_reg_imm (bvcomp RTL.mem_wordsize ((_ zero_extend 1) (_ bv1 1))))) (not (= (_ bv1 1) RTL.is_beq_bne_blt_bge_bltu_bgeu))) (= RTL.mem_do_rinst (bvcomp RTL.cpu_state ((_ zero_extend 4) (_ bv8 4)))))) (or (or (or (not (= (bvnot RTL.latched_branch) (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))))) (not (= (_ bv3 2) RTL.mem_wordsize))) (not (= (_ bv8 4) (concat RTL.instr_rdinstrh (concat RTL.instr_rdinstr (concat RTL.instr_rdcycleh RTL.instr_rdcycle)))))) (= RTL.latched_branch RTL.instr_rdinstrh))) (or (or (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2)))) (not (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6)))))) (not (= (ite (= (bvcomp RTL.mem_state (_ bv3 2)) (_ bv1 1)) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state) RTL.mem_state) (ite (= RTL.mem_do_rdata (_ bv1 1)) RTL.mem_wordsize (ite (= (bvor RTL.instr_lb RTL.instr_lbu) (_ bv1 1)) (_ bv2 2) (ite (= (bvor RTL.instr_lh RTL.instr_lhu) (_ bv1 1)) (_ bv1 2) (ite (= RTL.instr_lw (_ bv1 1)) (_ bv0 2) RTL.mem_wordsize)))))))) (or (not (= (_ bv2 2) (concat (bvcomp RTL.cpu_state ((_ zero_extend 5) (_ bv4 3))) (bvcomp RTL.cpu_state ((_ zero_extend 7) (_ bv1 1)))))) (not (= (_ bv1 1) RTL.decoder_pseudo_trigger)))) (or (or (or (or (or (or (not (= (_ bv1 1) RTL.mem_valid)) (not (= (_ bv1 1) RTL.mem_do_rdata))) (= (bvcomp RTL.mem_state (_ bv3 2)) RTL.trap)) (not (= (_ bv2 2) (concat (bvcomp RTL.cpu_state ((_ zero_extend 5) (_ bv4 3))) (bvcomp RTL.cpu_state ((_ zero_extend 7) (_ bv1 1))))))) (= (bvcomp RTL.mem_wordsize ((_ zero_extend 1) (_ bv1 1))) (ite (distinct RTL.mem_wordsize (_ bv0 2)) (_ bv1 1) (_ bv0 1)))) (= (_ bv1 1) RTL.mem_do_prefetch)) (not (= RTL.mem_do_prefetch (bvcomp RTL.mem_wordsize (_ bv2 2)))))) (or (or (or (or (or (or (not (= (_ bv1 1) RTL.mem_valid)) (not (= (_ bv1 1) RTL.mem_do_rdata))) (= (_ bv1 1) RTL.decoder_trigger)) (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvor RTL.decoder_trigger RTL.do_waitirq))) (not (= RTL.latched_branch (bvcomp RTL.mem_wordsize ((_ zero_extend 1) (_ bv1 1)))))) (not (= (bvcomp RTL.mem_wordsize (_ bv2 2)) (ite (not (distinct RTL.mem_wordsize (_ bv0 2))) (_ bv1 1) (_ bv0 1)))))) (or (or (not (= (_ bv1 1) (bvor RTL.mem_do_rinst RTL.mem_do_rdata))) (not (= (_ bv1 1) RTL.decoder_trigger))) (not (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 4) (_ bv8 4))))))) (or (or (or (or (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2)))) (not (= RTL.latched_branch RTL.mem_valid))) (= RTL.mem_valid RTL.do_waitirq)) (not (= (_ bv1 1) (bvcomp RTL.mem_wordsize (_ bv2 2))))) (= RTL.mem_do_rdata (bvcomp RTL.mem_wordsize ((_ zero_extend 1) (_ bv1 1)))))) (or (or (or (or (or (not (= (_ bv1 1) RTL.trap)) (not (= (_ bv1 1) RTL.mem_instr))) (= RTL.mem_do_rinst RTL.is_alu_reg_imm)) (not (= (_ bv3 2) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state)))) (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) RTL.mem_valid)) (not (= RTL.instr_jalr RTL.mem_instr)))) (or (or (or (not (= RTL.latched_branch RTL.mem_valid)) (not (= (_ bv5 3) (concat RTL.instr_slt (concat RTL.instr_slti RTL.instr_blt))))) (not (= RTL.latched_branch RTL.instr_slt))) (not (= RTL.latched_branch RTL.decoder_pseudo_trigger)))) (or (or (or (or (not (= RTL.latched_branch RTL.mem_valid)) (not (= (_ bv3 2) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state)))) (= (bvcomp RTL.mem_state (_ bv3 2)) RTL.instr_bne)) (not (= RTL.latched_branch RTL.decoder_pseudo_trigger))) (= RTL.latched_branch RTL.instr_bne))) (or (or (or (or (or (or (or (or (= (_ bv1 1) RTL.mem_do_wdata) (= (_ bv1 1) RTL.mem_do_rinst)) (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2))))) (= (_ bv1 1) RTL.decoder_trigger)) (not (= (_ bv1 1) RTL.mem_instr))) (not (= RTL.latched_branch RTL.mem_valid))) (= RTL.mem_do_rinst RTL.is_alu_reg_imm)) (= RTL.latched_branch RTL.instr_jal)) (= RTL.latched_branch RTL.mem_do_wdata))) (or (or (or (not (= (_ bv1 1) RTL.latched_branch)) (= (_ bv1 1) RTL.instr_srai)) (not (= RTL.instr_srai ((_ extract 7 7) RTL.mem_rdata_q)))) (= (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))) ((_ extract 7 7) RTL.mem_rdata_q)))) (or (or (or (or (or (or (not (= (_ bv1 1) RTL.latched_branch)) (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2))))) (not (= RTL.latched_branch RTL.is_alu_reg_imm))) (not (= RTL.mem_do_rinst RTL.decoder_trigger))) (= RTL.mem_valid (bvand (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) RTL.decoder_trigger))) (not (= RTL.is_jalr_addi_slti_sltiu_xori_ori_andi RTL.mem_instr))) (= RTL.latched_branch RTL.instr_jal))) (or (or (or (or (= (_ bv1 1) RTL.instr_lhu) (= (_ bv1 1) RTL.instr_lbu)) (= RTL.instr_slti (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))))) (= (distinct (concat RTL.instr_lhu (concat RTL.instr_lbu RTL.instr_lw)) (_ bv0 3)) (= RTL.instr_slti (_ bv0 1)))) (not (= (_ bv2 2) (ite (= RTL.instr_lw (_ bv1 1)) (_ bv0 2) RTL.mem_wordsize))))) (or (or (or (or (not (= (_ bv1 1) RTL.decoder_trigger)) (= (_ bv1 1) RTL.decoder_pseudo_trigger)) (not (= (_ bv1 1) (bvcomp ((_ extract 31 12) RTL.mem_rdata_q) (_ bv819202 20))))) (not (= (_ bv1 4) ((_ extract 11 8) RTL.mem_rdata_q)))) (not (= ((_ extract 19 15) RTL.mem_rdata_q) RTL.decoded_rd)))) (or (or (or (not (= (_ bv1 1) RTL.decoder_trigger)) (not (= (_ bv0 5) RTL.decoded_rd))) (= (_ bv1 1) RTL.decoder_pseudo_trigger)) (not (= (_ bv1 4) ((_ extract 11 8) RTL.mem_rdata_q))))) (or (or (not (= (_ bv1 1) RTL.mem_do_wdata)) (not (= (_ bv1 1) RTL.decoder_trigger))) (not (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 4) (_ bv8 4))))))) (or (or (or (or (or (or (not (= (_ bv1 1) (ite (distinct RTL.mem_wordsize (_ bv0 2)) (_ bv1 1) (_ bv0 1)))) (= RTL.latched_branch (ite (distinct RTL.mem_wordsize (_ bv0 2)) (_ bv1 1) (_ bv0 1)))) (= (_ bv1 1) RTL.instr_sra)) (= (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))) (bvor RTL.instr_sll RTL.instr_slli))) (not (= RTL.latched_branch RTL.instr_sll))) (= RTL.instr_sra RTL.instr_slti)) (= RTL.instr_slli RTL.instr_slti))) (or (or (= RTL.latched_branch (ite (distinct RTL.mem_wordsize (_ bv0 2)) (_ bv1 1) (_ bv0 1))) (= (_ bv1 1) (bvor RTL.instr_sll RTL.instr_slli))) (= (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))) (bvor RTL.instr_sll RTL.instr_slli)))) (or (or (or (not (= (_ bv1 1) (bvcomp RTL.mem_wordsize (_ bv2 2)))) (= (_ bv1 1) RTL.instr_jalr)) (not (= RTL.instr_jalr RTL.instr_and))) (= RTL.instr_and (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6)))))) (or (or (or (or (or (not (= (_ bv1 1) RTL.decoder_trigger)) (= (_ bv1 1) RTL.decoder_pseudo_trigger)) (not (= (_ bv3 4) ((_ extract 11 8) RTL.mem_rdata_q)))) (not (= (_ bv0 5) ((_ extract 24 20) RTL.mem_rdata_q)))) (not (= ((_ extract 19 15) RTL.mem_rdata_q) ((_ extract 24 20) RTL.mem_rdata_q)))) (not (= ((_ extract 19 15) RTL.mem_rdata_q) RTL.decoded_rd)))) (or (or (or (not (= (_ bv1 1) (bvcomp RTL.mem_wordsize (_ bv2 2)))) (not (= (_ bv1 1) RTL.instr_srl))) (= RTL.instr_srl ((_ extract 7 7) RTL.mem_rdata_q))) (= (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))) ((_ extract 7 7) RTL.mem_rdata_q)))) (or (or (or (not (= (_ bv1 1) (bvcomp RTL.mem_wordsize (_ bv2 2)))) (not (= (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))) ((_ extract 7 7) RTL.mem_rdata_q)))) (not (= (bvcomp ((_ extract 14 12) RTL.mem_rdata_q) (_ bv7 3)) (bvcomp ((_ extract 31 12) RTL.mem_rdata_q) (_ bv819202 20))))) (= ((_ extract 7 7) RTL.mem_rdata_q) (bvand (bvcomp ((_ extract 6 0) RTL.mem_rdata_q) (_ bv115 7)) (bvcomp ((_ extract 31 12) RTL.mem_rdata_q) (_ bv819202 20)))))) (or (or (or (or (or (not (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= (_ bv1 1) RTL.instr_add)) (= RTL.instr_blt (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))))) (not (= RTL.latched_branch RTL.instr_blt))) (= RTL.instr_add (bvcomp RTL.mem_wordsize (_ bv2 2))))) (or (or (or (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6)))) (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= RTL.instr_bge (bvcomp RTL.mem_wordsize (_ bv2 2)))) (not (= RTL.latched_branch RTL.instr_bge)))) (or (or (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6)))) (= RTL.latched_branch (ite (distinct RTL.mem_wordsize (_ bv0 2)) (_ bv1 1) (_ bv0 1)))) (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7)))))) (or (or (or (or (or (not (= (_ bv1 1) RTL.mem_do_wdata)) (not (= (_ bv1 1) RTL.mem_valid))) (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvcomp RTL.cpu_state ((_ zero_extend 3) (_ bv16 5))))) (= (ite (distinct RTL.mem_state (_ bv0 2)) (_ bv1 1) (_ bv0 1)) (bvor RTL.decoder_trigger RTL.do_waitirq))) (not (= (_ bv1 1) (bvcomp RTL.mem_wordsize (_ bv2 2)))))) (or (or (or (or (or (or (= (_ bv1 1) RTL.latched_branch) (not (= (_ bv1 1) RTL.mem_do_wdata))) (not (= (_ bv1 1) RTL.mem_valid))) (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvcomp RTL.mem_state (_ bv2 2)))) (not (= (bvcomp RTL.cpu_state ((_ zero_extend 6) (_ bv2 2))) (bvcomp RTL.mem_state (_ bv2 2))))) (not (= RTL.do_waitirq (bvor RTL.decoder_trigger RTL.do_waitirq))))) (or (not (= (_ bv1 1) RTL.mem_valid)) (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2)))))) (or (or (= (_ bv1 1) RTL.latched_branch) (= RTL.latched_branch RTL.mem_valid)) (= RTL.latched_branch (bvcomp RTL.mem_state (_ bv3 2))))) (or (or (or (or (not (= (_ bv1 1) RTL.latched_branch)) (not (= (_ bv1 1) RTL.mem_valid))) (= (_ bv1 1) RTL.trap)) (= (bvcomp RTL.mem_state (_ bv3 2)) RTL.trap)) (not (= (distinct RTL.mem_state (_ bv0 2)) (distinct (concat (bvcomp RTL.cpu_state ((_ zero_extend 5) (_ bv4 3))) (bvcomp RTL.cpu_state ((_ zero_extend 7) (_ bv1 1)))) (_ bv0 2)))))) (or (or (or (or (not (= (_ bv1 1) RTL.latched_branch)) (= (_ bv1 1) RTL.mem_do_rinst)) (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2))))) (not (= (_ bv1 1) (bvor RTL.mem_do_rinst RTL.mem_do_rdata)))) (not (= RTL.latched_branch RTL.mem_valid)))) (or (or (or (or (not (= (_ bv1 1) RTL.trap)) (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) RTL.mem_do_rdata)) (= RTL.mem_do_rinst (bvcomp RTL.mem_state (_ bv3 2)))) (= RTL.mem_do_rinst (ite (distinct RTL.mem_state (_ bv0 2)) (_ bv1 1) (_ bv0 1)))) (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) RTL.mem_valid))) (or (or (or (or (not (= (_ bv1 1) RTL.mem_valid)) (not (= (_ bv1 1) RTL.mem_do_rdata))) (not (= RTL.latched_branch RTL.latched_store))) (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvor RTL.decoder_trigger RTL.do_waitirq)))) (or (or (or (not (= (_ bv1 1) RTL.latched_store)) (not (= (_ bv1 1) RTL.mem_valid))) (not (= (_ bv1 1) RTL.mem_do_rdata))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvor RTL.decoder_trigger RTL.do_waitirq)))) (or (or (or (or (= (_ bv1 1) RTL.latched_branch) (not (= (_ bv1 1) RTL.latched_store))) (not (= (_ bv1 1) RTL.mem_valid))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvcomp RTL.cpu_state ((_ zero_extend 3) (_ bv16 5))))) (= (ite (distinct RTL.mem_state (_ bv0 2)) (_ bv1 1) (_ bv0 1)) (bvor RTL.decoder_trigger RTL.do_waitirq)))) (or (or (or (not (= (_ bv1 1) RTL.latched_branch)) (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2))))) (not (= RTL.mem_do_rinst RTL.decoder_trigger))) (= RTL.mem_valid (bvand (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) RTL.decoder_trigger)))) (or (or (or (not (= (_ bv1 1) RTL.mem_valid)) (= (_ bv1 1) RTL.decoder_trigger)) (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) (bvor RTL.decoder_trigger RTL.do_waitirq))) (not (= (_ bv3 2) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state))))) (or (or (or (not (= (_ bv1 1) RTL.mem_valid)) (= (_ bv1 1) RTL.decoder_trigger)) (not (= (_ bv3 2) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state)))) (= RTL.mem_do_rinst (bvcomp RTL.cpu_state ((_ zero_extend 4) (_ bv8 4)))))) (or (or (or (or (or (or (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2)))) (= RTL.latched_branch RTL.mem_valid)) (not (= RTL.decoder_trigger (bvor (bvor RTL.instr_srl RTL.instr_srli) RTL.instr_sra)))) (not (= RTL.instr_lw (bvor (bvor RTL.instr_srl RTL.instr_srli) RTL.instr_sra)))) (not (= (_ bv0 2) (concat RTL.instr_lbu RTL.instr_lw)))) (not (= (_ bv8 4) (concat RTL.instr_rdinstrh (concat RTL.instr_rdinstr (concat RTL.instr_rdcycleh RTL.instr_rdcycle)))))) (= RTL.latched_branch RTL.instr_rdinstrh))) (or (or (or (or (not (= (_ bv1 1) RTL.mem_valid)) (= (_ bv1 1) RTL.trap)) (not (= RTL.latched_branch RTL.decoder_trigger))) (not (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 4) (_ bv8 4)))))) (= (bvcomp RTL.mem_state (_ bv3 2)) RTL.trap))) (or (or (or (not (= (_ bv1 1) RTL.mem_valid)) (not (= (_ bv1 1) RTL.mem_do_rdata))) (not (= (_ bv3 2) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state)))) (not (= (_ bv2 2) (concat (bvcomp RTL.cpu_state ((_ zero_extend 5) (_ bv4 3))) (bvcomp RTL.cpu_state ((_ zero_extend 7) (_ bv1 1)))))))) (or (or (or (not (= (_ bv1 1) (bvor RTL.mem_do_rinst RTL.mem_do_rdata))) (not (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 4) (_ bv8 4)))))) (= RTL.mem_valid (bvand (bvcomp RTL.mem_state (_ bv3 2)) RTL.mem_do_rinst))) (not (= (_ bv3 2) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state))))) (or (or (or (or (or (not (= (_ bv1 1) RTL.mem_instr)) (= RTL.mem_do_rinst RTL.is_alu_reg_imm)) (not (= (_ bv3 2) (ite (= RTL.mem_do_rinst (_ bv1 1)) (_ bv0 2) RTL.mem_state)))) (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) RTL.mem_valid)) (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) (bvcomp RTL.mem_state (_ bv3 2)))) (not (= RTL.instr_jalr RTL.mem_instr)))) (or (or (or (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2)))) (not (= RTL.latched_branch RTL.mem_valid))) (not (= (_ bv5 3) (concat RTL.instr_slt (concat RTL.instr_slti RTL.instr_blt))))) (not (= RTL.latched_branch RTL.instr_slt)))) (or (or (or (or (not (= RTL.latched_branch RTL.mem_valid)) (= (bvcomp RTL.mem_state (_ bv3 2)) RTL.instr_bne)) (not (= (_ bv8 4) (concat RTL.instr_rdinstrh (concat RTL.instr_rdinstr (concat RTL.instr_rdcycleh RTL.instr_rdcycle)))))) (not (= RTL.latched_branch RTL.instr_rdinstrh))) (= RTL.latched_branch RTL.instr_bne))) (or (or (not (= (_ bv1 1) RTL.latched_branch)) (not (= (_ bv1 1) RTL.mem_valid))) (not (= RTL.latched_branch (bvcomp RTL.mem_state (_ bv3 2)))))) (or (or (or (or (or (or (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2)))) (= RTL.latched_branch RTL.mem_valid)) (= (_ bv1 1) RTL.instr_lhu)) (= (_ bv1 1) RTL.instr_lbu)) (= (_ bv1 1) RTL.instr_lw)) (= RTL.instr_slti (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))))) (= (distinct (concat RTL.instr_lhu (concat RTL.instr_lbu RTL.instr_lw)) (_ bv0 3)) (= RTL.instr_slti (_ bv0 1))))) (or (or (or (or (or (not (= (_ bv1 1) RTL.mem_do_wdata)) (not (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 4) (_ bv8 4)))))) (= (_ bv1 1) (bvcomp ((_ extract 6 0) RTL.mem_rdata_q) ((_ zero_extend 3) (_ bv11 4))))) (= RTL.mem_valid (bvand (bvcomp ((_ extract 6 0) RTL.mem_rdata_q) ((_ zero_extend 3) (_ bv11 4))) (bvcomp ((_ extract 31 25) RTL.mem_rdata_q) ((_ zero_extend 6) (_ bv1 1)))))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvcomp ((_ extract 31 25) RTL.mem_rdata_q) ((_ zero_extend 5) (_ bv3 2))))) (not (= (bvcomp RTL.cpu_state ((_ zero_extend 6) (_ bv2 2))) (bvcomp ((_ extract 31 25) RTL.mem_rdata_q) ((_ zero_extend 5) (_ bv3 2))))))) (or (or (or (or (or (not (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= RTL.latched_branch RTL.mem_valid)) (= RTL.latched_branch (bvcomp RTL.mem_state (_ bv3 2)))) (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= RTL.instr_blt (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))))) (not (= RTL.latched_branch RTL.instr_blt)))) (or (or (or (= RTL.latched_branch RTL.mem_valid) (= RTL.latched_branch (bvcomp RTL.mem_state (_ bv3 2)))) (not (= (_ bv1 1) RTL.instr_slti))) (not (= RTL.instr_slti (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))))))) (or (or (or (or (or (not (= RTL.latched_branch (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= RTL.latched_branch RTL.mem_valid)) (= RTL.latched_branch (bvcomp RTL.mem_state (_ bv3 2)))) (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (= RTL.instr_slti (bvcomp RTL.cpu_state ((_ zero_extend 2) (_ bv32 6))))) (not (= RTL.latched_branch RTL.instr_slti)))) (or (or (not (= (_ bv1 1) RTL.mem_valid)) (= RTL.latched_branch (bvcomp RTL.mem_state (_ bv3 2)))) (not (= RTL.latched_branch RTL.decoder_trigger)))) (or (not (= (_ bv1 1) RTL.mem_valid)) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvor RTL.decoder_trigger RTL.do_waitirq)))) (or (or (not (= (_ bv1 1) RTL.mem_valid)) (= (_ bv1 1) RTL.trap)) (= (bvcomp RTL.mem_state (_ bv3 2)) RTL.trap))) (or (or (not (= (_ bv1 1) (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))))) (not (= (bvcomp RTL.cpu_state ((_ zero_extend 1) (_ bv64 7))) RTL.mem_valid))) (= (bvcomp RTL.mem_state (_ bv3 2)) (bvcomp RTL.cpu_state ((_ zero_extend 6) (_ bv2 2)))))) (not (and (and (and (and (and (and (and (and (and (and (and (and (and (= RTL.mem_do_rinst (_ bv1 1)) (= RTL.mem_instr (_ bv1 1))) (= RTL.cpu_state (_ bv64 8))) (= RTL.instr_retirq (_ bv0 1))) (= RTL.instr_jal (_ bv0 1))) (= RTL.mem_valid (_ bv1 1))) (= RTL.latched_branch (_ bv0 1))) (= RTL.latched_store (_ bv0 1))) (= RTL.is_alu_reg_imm (_ bv1 1))) (= RTL.decoded_rd (_ bv0 5))) (= RTL.mem_state (_ bv3 2))) (= RTL.is_jalr_addi_slti_sltiu_xori_ori_andi (_ bv1 1))) (= RTL.decoder_trigger_q (_ bv0 1))) (= RTL.rvfi_trap (_ bv0 1))))))
(define-fun assumption.2 ((RTL.instr_lui (_ BitVec 1)) (RTL.mem_valid (_ BitVec 1)) (RTL.decoder_trigger_q (_ BitVec 1)) (RTL.instr_jalr (_ BitVec 1)) (RTL.latched_store (_ BitVec 1)) (RTL.instr_and (_ BitVec 1)) (RTL.instr_andi (_ BitVec 1)) (RTL.mem_do_rinst (_ BitVec 1)) (RTL.instr_auipc (_ BitVec 1)) (RTL.mem_state (_ BitVec 2)) (RTL.latched_branch (_ BitVec 1)) (RTL.mem_instr (_ BitVec 1)) (RTL.cpu_state (_ BitVec 8)) (RTL.instr_jal (_ BitVec 1)) (RTL.instr_retirq (_ BitVec 1)) (RTL.rvfi_trap (_ BitVec 1))) Bool (and (and (and (and true (or (or (or (or (= (_ bv1 1) (ite (distinct RTL.mem_state (_ bv0 2)) (_ bv1 1) (_ bv0 1))) (not (= (_ bv1 1) RTL.instr_jalr))) (= (_ bv1 1) (bvor RTL.instr_andi RTL.instr_and))) (= RTL.mem_valid RTL.instr_andi)) (not (= (_ bv2 3) (concat RTL.instr_jal (concat RTL.instr_auipc RTL.instr_lui)))))) (or (not (= (_ bv1 1) RTL.mem_valid)) (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv3 2)))))) (or (not (= (_ bv1 1) RTL.mem_valid)) (= (_ bv1 1) (ite (distinct RTL.mem_state (_ bv0 2)) (_ bv1 1) (_ bv0 1))))) (not (and (and (and (and (and (and (and (and (and (and (= RTL.mem_valid (_ bv1 1)) (= RTL.decoder_trigger_q (_ bv0 1))) (= RTL.rvfi_trap (_ bv0 1))) (= RTL.instr_retirq (_ bv0 1))) (= RTL.instr_jal (_ bv0 1))) (= RTL.latched_store (_ bv0 1))) (= RTL.cpu_state (_ bv64 8))) (= RTL.mem_instr (_ bv1 1))) (= RTL.latched_branch (_ bv0 1))) (= RTL.mem_state (_ bv0 2))) (= RTL.mem_do_rinst (_ bv1 1))))))
(define-fun assumption.3 ((RTL.mem_instr (_ BitVec 1)) (RTL.is_alu_reg_imm (_ BitVec 1)) (RTL.mem_do_rinst (_ BitVec 1)) (RTL.instr_jal (_ BitVec 1)) (RTL.mem_do_wdata (_ BitVec 1)) (RTL.mem_do_rdata (_ BitVec 1)) (RTL.trap (_ BitVec 1)) (RTL.latched_store (_ BitVec 1)) (RTL.is_jalr_addi_slti_sltiu_xori_ori_andi (_ BitVec 1)) (RTL.compressed_instr (_ BitVec 1)) (RTL.decoder_trigger_q (_ BitVec 1)) (RTL.mem_state (_ BitVec 2)) (RTL.instr_retirq (_ BitVec 1)) (RTL.mem_valid (_ BitVec 1)) (RTL.mem_do_prefetch (_ BitVec 1)) (RTL.latched_branch (_ BitVec 1))) Bool (and (and true (or (or (= (_ bv1 1) RTL.mem_do_wdata) (not (= (_ bv1 1) RTL.mem_valid))) (not (= (_ bv1 1) (bvcomp RTL.mem_state (_ bv2 2)))))) (not (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= RTL.instr_jal (_ bv0 1)) (= RTL.mem_do_rdata (_ bv0 1))) (= RTL.trap (_ bv0 1))) (= RTL.mem_instr (_ bv1 1))) (= RTL.is_alu_reg_imm (_ bv1 1))) (= RTL.mem_do_rinst (_ bv0 1))) (= RTL.latched_branch (_ bv0 1))) (= RTL.mem_do_prefetch (_ bv1 1))) (= RTL.mem_valid (_ bv1 1))) (= RTL.instr_retirq (_ bv0 1))) (= RTL.mem_state (_ bv2 2))) (= RTL.decoder_trigger_q (_ bv0 1))) (= RTL.mem_do_wdata (_ bv0 1))) (= RTL.compressed_instr (_ bv0 1))) (= RTL.is_jalr_addi_slti_sltiu_xori_ori_andi (_ bv1 1))) (= RTL.latched_store (_ bv0 1))))))