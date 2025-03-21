
uppercase.bin:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <_start>:
   10074:	00002537          	lui	a0,0x2

00010078 <loop_start>:
   10078:	00050283          	lb	t0,0(a0) # 2000 <__DATA_BEGIN__>
   1007c:	02028463          	beqz	t0,100a4 <end_program>
   10080:	06100313          	li	t1,97
   10084:	07a00393          	li	t2,122
   10088:	0062c863          	blt	t0,t1,10098 <skip>
   1008c:	0053c663          	blt	t2,t0,10098 <skip>
   10090:	02000e13          	li	t3,32
   10094:	41c282b3          	sub	t0,t0,t3

00010098 <skip>:
   10098:	00550023          	sb	t0,0(a0)
   1009c:	00150513          	addi	a0,a0,1
   100a0:	fd9ff06f          	j	10078 <loop_start>

000100a4 <end_program>:
   100a4:	0000006f          	j	100a4 <end_program>
