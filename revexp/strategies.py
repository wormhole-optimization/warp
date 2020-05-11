import matplotlib.pyplot as plt
import numpy as np

# plt.rcParams.update({'font.size': 13})
# plt.rcParams["font.family"] = "Times New Roman"

fig, axs = plt.subplots(
    1, 1,
    sharey=True,
    figsize=(5, 3),
    gridspec_kw={'wspace': 0}
)

ax = axs
# ax3.set_xlabel('Data Size (Input Dimensions)')
ax.set_ylabel(ylabel='Run Time [sec]') #, labelpad=-2)
ax.set_yscale('log')

width = 0.2

# GLM L2SVM MLogReg ALS PNMF

sml = [213.1432, 237.993, 127.301, 100.579, 46.1356]
silp = [21.6916, 213.153, 120.177, 63.7024, 13.7282]
sgre = [21.907, 218.029, 119.038, 63.543, 13.61]
dgre = [21.4, 0, 0, 64.72, 13.61]
timeout = [0, 1000, 1000, 0, 0]

labels = ["ALS", "GLM", "SVM", "MLR", "PNMF"]
x = np.arange(len(labels))

ax.bar(x-1.5*width, sml,        width, label='SystemML',      ec='black', color='0.2')
ax.bar(x-0.5*width, dgre,        width, label='D+greedy',    ec='black', color='0.5')
ax.bar(x-0.5*width, timeout,        width, label='timeout',    ec='black', color='white', hatch="..")
ax.bar(x+0.5*width, silp, width, label='S+ILP', ec='black', color='white', hatch='//')
ax.bar(x+1.5*width, sgre, width, label='S+greedy', ec='black', color='white')

# ax.set_title(benchmark["name"])
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.label_outer()

ax.legend(prop={'size': 8})

plt.ylim(top=1000)
plt.ylim(bottom=1)
plt.tight_layout()
plt.savefig('strategy.pdf')
