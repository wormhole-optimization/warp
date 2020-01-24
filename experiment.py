import matplotlib.pyplot as plt
import numpy as np

# Some example data to display

width = 0.2

fig, axs = plt.subplots(1, 5, sharey='row',
                        gridspec_kw={'hspace': 0, 'wspace': 0}, figsize=(20,4))
(ax1, ax2, ax3, ax4, ax5) = axs

# k-means
labels = ['1Mx10', '1Mx100', '10Mx10', '10Mx100']
opt0 = [13.345, 22.8758, 114.7328, 217.0804]
opt2_nofuse = [5, 6, 41, 75.1746]
opt2_fuse = [4, 4.8, 33, 60]
saturate_la = [5, 6, 41, 75]

x = np.arange(len(labels))

ax1.set_ylabel('Execution Time [sec]')
ax1.set_yscale('log')

for ax in axs:

    ax.bar(x-1.5*width, opt0,        width, label='no opt', ec='black', color='0.2')
    ax.bar(x-0.5*width, opt2_nofuse, width, label='SystemML', ec='black', color='0.5')
    ax.bar(x+0.5*width, opt2_fuse,   width, label='saturate RA', ec='black', color='white')
    ax.bar(x+1.5*width, saturate_la, width, label='saturate LA', ec='black', color='white', hatch='//')

    ax.set_title('K-Means Execution Time')
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax1.legend()
    ax3.set_xlabel('Data Size (Input Dimensions)')

# ax2.bar(labels, opt0)
# ax2.bar(labels, opt0)
# ax3.bar(labels, opt0)
# ax3.bar(labels, opt0)
# ax4.bar(labels, opt0)
# ax4.bar(labels, opt0)
# ax5.bar(labels, opt0)
# ax5.bar(labels, opt0)

for ax in axs.flat:
    ax.label_outer()

plt.tight_layout()
plt.show()
