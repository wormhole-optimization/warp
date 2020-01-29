import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({'font.size': 13})

fig, ax = plt.subplots()
width = 0.2

sysml  = [3, 2.8, 3, 3.28, 4.7328]
greedy = [4, 4.8, 4.8, 4.8, 13]
ilp    = [5, 6, 41, 21, 31]

labels = ['GLM', 'L2SVM', 'MLogReg', 'ALS', 'PNMF']
x = np.arange(len(labels))

ax.bar(x-1.5*width, sysml,  width, label='SystemML', ec='black', color='0.2')
ax.bar(x-0.5*width, greedy, width, label='greedy',   ec='black', color='0.5')
ax.bar(x+0.5*width, ilp,    width, label='ILP',      ec='black', color='white')

ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.set_xlabel('Algorithm')
ax.set_ylabel(ylabel='Compile Time [sec]')
ax.label_outer()
ax.legend()

plt.tight_layout()
plt.savefig('compilevsml.pdf', format='pdf')
