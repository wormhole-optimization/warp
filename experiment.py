import matplotlib.pyplot as plt
import numpy as np

# plt.rcParams.update({'font.size': 13})

width = 0.2

fig, axs = plt.subplots(1, 5, sharex=True, sharey=True, figsize=(12, 4), gridspec_kw={'hspace': 0, 'wspace': 0})
(ax1, ax2, ax3, ax4, ax5) = axs

# k-means
labels = ['1Mx10', '10Mx10', '10Mx100']
opt0 = [13.345, 22.8758, 114.7328]
opt2_nofuse = [5, 6, 41]
opt2_fuse = [4, 4.8, 33]
saturate_la = [5, 6, 41]

x = np.arange(len(labels))
ax1.set_ylabel(ylabel='Run Time [sec]', labelpad=-6)
ax1.set_yscale('log')

for ax in axs.flat:

    ax.bar(x-1.5*width, opt0,        width, label='no opt', ec='black', color='0.2')
    ax.bar(x-0.5*width, opt2_nofuse, width, label='SystemML', ec='black', color='0.5')
    ax.bar(x+0.5*width, opt2_fuse,   width, label='saturate RA', ec='black', color='white')
    ax.bar(x+1.5*width, saturate_la, width, label='saturate LA', ec='black', color='white', hatch='//')

    ax.set_title('K-Means Execution Time')
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax1.legend()
    ax3.set_xlabel('Data Size (Input Dimensions)')

for ax in axs.flat:
    ax.label_outer()

yl = plt.ylim()

plt.tight_layout()
plt.savefig('runtime1.pdf', format='pdf')

# fig, axs = plt.subplots(1, 2, sharex=True, sharey=True, figsize=(8, 4))
# (ax1, ax2) = axs
# 
# plt.ylim(yl)
# 
# # k-means
# labels = ['1Mx10', '1Mx100', '10Mx10', '10Mx100']
# opt0 = [100, 20, 100, 20]
# opt2_nofuse = [5, 6, 4, 7]
# opt2_fuse = [4, 4.8, 3, 6]
# saturate_la = [5, 6, 4, 7]
# 
# x = np.arange(len(labels))
# ax1.set_ylabel('Execution Time [sec]')
# ax1.set_yscale('log')
# 
# for ax in axs.flat:
# 
#     ax.bar(x-1.5*width, opt0,        width, label='no opt', ec='black', color='0.2')
#     ax.bar(x-0.5*width, opt2_nofuse, width, label='SystemML', ec='black', color='0.5')
#     ax.bar(x+0.5*width, opt2_fuse,   width, label='saturate RA', ec='black', color='white')
#     ax.bar(x+1.5*width, saturate_la, width, label='saturate LA', ec='black', color='white', hatch='//')
# 
#     ax.set_title('K-Means Execution Time')
#     ax.set_xticks(x)
#     ax.set_xticklabels(labels)
# 
# for ax in axs.flat:
#     ax.label_outer()
# 
# plt.tight_layout()
# plt.savefig('runtime2.pdf', format='pdf')
