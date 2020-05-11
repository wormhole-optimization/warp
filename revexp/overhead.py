import numpy as np
import matplotlib.pyplot as plt

plt.rcParams.update({'font.size': 9})

benchmarks = ['G', 'L', 'A', 'P', 'M']

N = len(benchmarks)

results = [
  {
    "method": "DFS+greedy",
    "translation": [0.06, 0.01, 0.09, 0.02, 0.03],
    "saturation" : [0.32, 10, 10, 0.13, 0.06],
    "extraction" : [0.005, 0.0, 0.0, 0.003, 0.001],
    "timeout" : [0.0, 10, 10, 0.0, 0.0],
    "sysml" : (0, 0, 0, 0, 0)
  },
  {
    "method": "sample+greedy",
    "translation": [0.06, 0.01, 0.09, 0.02, 0.03],
    "saturation" : [0.31, 0.29, 0.56, 0.28, 0.09],
    "extraction" : [0.02, 0.01, 0.07, 0.02, 0.001],
    "timeout" : [0.0, 0.0, 0.0, 0.0, 0.0],
    "sysml" : (0, 0, 0, 0, 0)
  },
  {
    "method": "sample+ILP",
    "translation": [0.06, 0.01, 0.09, 0.02, 0.03],
    "saturation" : [0.43, 0.35, 0.43, 0.5, 0.05],
    "extraction" : [0.67, 0.81, 1.53, 0.15, 0.06],
    "timeout" : [0.0, 0.0, 0.0, 0.0, 0.0],
    "sysml" : (0, 0, 0, 0, 0)
  },
  {
    "method": "SystemML",
    "translation": [0.0, 0.0, 0.0, 0.0, 0.0],
    "saturation" : [0.0, 0.0, 0.0, 0.0, 0.0],
    "extraction" : [0.0, 0.0, 0.0, 0.0, 0.0],
    "timeout" : [0.0, 0.0, 0.0, 0.0, 0.0],
    "sysml" : (1.72, 0.71, 0.52, 0.39, 0.08)
  },
]
ind = np.arange(N)    # the x locations for the groups
width = 0.5       # the width of the bars: can also be len(x) sequence

# fig, axs = plt.subplots(2, 2, sharey=True, figsize=(12, 4), gridspec_kw={'wspace': 0})
fig, axs = plt.subplots(1, 4, sharex=True, sharey=True, figsize=(5.5, 2), gridspec_kw={'wspace': 0})


(ax1, ax2, ax3, ax4) = axs
ax1.set_ylabel(ylabel='Compile Time [sec]')
# ax1.set_xlabel(xlabel='Program')
# ax2.set_xlabel(xlabel='Program')
# ax3.set_xlabel(xlabel='Program')
# ax4.set_xlabel(xlabel='Program')

for i, ax in enumerate(axs.flat):
  ax.set_xticks(np.arange(N))
  ax.set_xticklabels(benchmarks)
  ax.set_yticks([0, 1, 2])
  benchmark = results[i]
  translation=benchmark["translation"]
  saturation =benchmark["saturation"]
  extraction =benchmark["extraction"]
  timeout =benchmark["timeout"]
  systemml =benchmark["sysml"]
  ax.bar(ind, translation, width, label='trans.', color='0.2', ec='black')
  ax.bar(ind, saturation, width, label='sat.', bottom=translation, color='0.5', ec='black')
  ax.bar(ind, extraction, width, label='extr.', bottom= np.array(translation) + np.array(saturation), color='white', ec='black', hatch='//')
  ax.bar(ind, systemml, width, label='SysML', color='white', ec='black')
  ax.bar(ind, timeout, width, label='TO', color='white', hatch='..')
  ax.set_title(benchmark["method"])

ax4.legend(prop={'size': 8})
# plt.legend((p1[0], p2[0], p3[0]), ('translation', 'saturation', 'extraction'))
handles, labels = ax4.get_legend_handles_labels()

plt.ylim(top=2.5)
plt.ylim(bottom=0)

# add a big axes, hide frame
# fig.add_subplot(111, frameon=False)
# hide tick and tick label of the big axes
# plt.tick_params(labelcolor='none', top=False, bottom=False, left=False, right=False)
# plt.xlabel("Program")
fig.text(0.5, 0.02, 'Program', ha='center')
# fig.legend(handles, labels, loc='lower center', ncol = 5, bbox_to_anchor=(0.5,0.8))
plt.tight_layout()
plt.savefig('compiletime.pdf', format='pdf')
