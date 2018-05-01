package network

import (
	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"

	"github.com/docker/swarmkit/api"
	"github.com/docker/swarmkit/manager/allocator/network/errors"

	// gomock code. usually, i would not use gomock, i would write a fake.
	// but because this component is almost entirely a shim between the caller
	// and the lower level interfaces, mocking them out will save a lot of
	// time and effort over building rather complex fakes.
	driver "github.com/docker/swarmkit/mocks/mock_driver"
	ipam "github.com/docker/swarmkit/mocks/mock_ipam"
	port "github.com/docker/swarmkit/mocks/mock_port"
	"github.com/golang/mock/gomock"
)

var _ = Describe("network.Allocator", func() {
	var (
		a *allocator

		// initial state, which will be passed to Restore befor each spec
		initNetworks []*api.Network
		initServices []*api.Service
		initTasks    []*api.Task
		initNodes    []*api.Node

		// mock sub-allocators
		mockCtrl   *gomock.Controller
		mockIpam   *ipam.MockAllocator
		mockDriver *driver.MockAllocator
		mockPort   *port.MockAllocator
	)

	BeforeEach(func() {
		// nil out the initialization lists so that they're fresh for every
		// test
		initNetworks = nil
		initServices = nil
		initTasks = nil
		initNodes = nil
		// set up the mocks, and create an Allocator that uses them
		mockCtrl = gomock.NewController(GinkgoT())
		mockIpam = ipam.NewMockAllocator(mockCtrl)
		mockDriver = driver.NewMockAllocator(mockCtrl)
		mockPort = port.NewMockAllocator(mockCtrl)

		a = newAllocatorWithComponents(mockIpam, mockDriver, mockPort)
	})

	AfterEach(func() {
		// don't forget to finish the mock
		mockCtrl.Finish()
	})

	Describe("Restoring", func() {
		var (
			err error
		)
		JustBeforeEach(func() {
			err = a.Restore(initNetworks, initServices, initTasks, initNodes)
		})

		Context("when there is no state to restore", func() {
			BeforeEach(func() {
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, []*api.NetworkAttachment{}).Return(nil)
				mockDriver.EXPECT().Restore(nil).Return(nil)
			})
			It("should return no error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
		})
		Context("when there are some networks allocated", func() {
			BeforeEach(func() {
				initNetworks = []*api.Network{
					{
						ID: "fooNet",
					},
					{
						ID: "localnet",
					},
				}
				// fooNet will be global, but localnet will be local
				mockDriver.EXPECT().IsNetworkNodeLocal(initNetworks[0]).Return(false, nil)
				mockDriver.EXPECT().IsNetworkNodeLocal(initNetworks[1]).Return(true, nil)
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(initNetworks, []*api.Endpoint{}, []*api.NetworkAttachment{}).Return(nil)
				mockDriver.EXPECT().Restore(initNetworks).Return(nil)
			})
			It("should return no error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
			It("should restore ipam and driver state", func() {
				// empty case, because this will actually be handled by gomock,
				// which will fail if it doesn't call restore with the
				// networks. this spec has been left here for documentation
				// purposes
			})
			It("should keep track of node-local networks", func() {
				Expect(a.nodeLocalNetworks).To(HaveKey("localnet"))
				Expect(a.nodeLocalNetworks["localnet"]).To(Equal(initNetworks[1]))
			})
		})
		Context("when there are some services allocated", func() {
			BeforeEach(func() {
				// service that are initialized
				initServices = []*api.Service{
					// an empty service, should not be included in restore, but
					// should be included in our services tracking map
					{ID: "service0"},
					// a fully allocated service, should be included in the
					// restore, and should be tracked in the "allocated" map
					{
						ID:          "service1",
						SpecVersion: &api.Version{Index: 1},
						Endpoint: &api.Endpoint{
							Spec: &api.EndpointSpec{
								Mode: api.ResolutionModeVirtualIP,
							},
							VirtualIPs: []*api.Endpoint_VirtualIP{
								{NetworkID: "nw1", Addr: "192.168.1.1/24"},
								{NetworkID: "nw2", Addr: "192.168.2.1/24"},
							},
						},
						Spec: api.ServiceSpec{
							Endpoint: &api.EndpointSpec{
								Mode: api.ResolutionModeVirtualIP,
							},
							Task: api.TaskSpec{
								Networks: []*api.NetworkAttachmentConfig{
									{Target: "nw1"},
									{Target: "nw2"},
								},
							},
						},
					},
					// Partially allocated service, should be included in the
					// IPAM and Port restore, but should not
					{
						ID:          "service2",
						SpecVersion: &api.Version{Index: 2},
						Endpoint: &api.Endpoint{
							Spec: &api.EndpointSpec{
								Mode: api.ResolutionModeVirtualIP,
							},
							VirtualIPs: []*api.Endpoint_VirtualIP{
								{NetworkID: "nw1", Addr: "192.168.1.1/24"},
							},
						},
						Spec: api.ServiceSpec{
							Endpoint: &api.EndpointSpec{},
						},
					},
				}

				endpoints := []*api.Endpoint{initServices[1].Endpoint, initServices[2].Endpoint}
				mockPort.EXPECT().Restore(endpoints)
				mockIpam.EXPECT().Restore(nil, endpoints, []*api.NetworkAttachment{})
				mockDriver.EXPECT().Restore(nil)
			})

			It("should not return an error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
			It("should restore ipam and port state of the service's endpoints", func() {
				// again, an empty spec, because this behavior is covered by
				// gomock doing its thing.
			})
			It("should mark service 0 & 1 as fully allocated, and not service 2", func() {
				Expect(a.services).To(And(
					HaveKey("service0"),
					HaveKey("service1"),
					Not(HaveKey("service2")),
				))
				Expect(a.services["service0"]).To(Equal(initServices[0]))
				Expect(a.services["service1"]).To(Equal(initServices[1]))
			})
		})
		Context("when some tasks are allocated", func() {
			BeforeEach(func() {
				initTasks = []*api.Task{
					// Empty task, should add any attachments
					{},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "foo"}, Addresses: []string{"192.168.1.4/24"}},
							{Network: &api.Network{ID: "bar"}, Addresses: []string{"192.168.2.4/24"}},
						},
					},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "baz"}, Addresses: []string{"192.168.3.4/24"}},
							{Network: &api.Network{ID: "bat"}, Addresses: []string{"192.168.4.4/24"}},
						},
					},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "local"}, Addresses: []string{"10.6.6.6"}},
						},
					},
				}

				// add the "local" network, which will be node-local
				local := &api.Network{
					ID: "local",
				}
				initNetworks = append(initNetworks, local)
				mockDriver.EXPECT().IsNetworkNodeLocal(local).Return(true, nil)

				attachments := append(initTasks[1].Copy().Networks, initTasks[2].Copy().Networks...)
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(initNetworks, []*api.Endpoint{}, attachments).Return(nil)
				mockDriver.EXPECT().Restore(initNetworks).Return(nil)
			})
			It("should not return an error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
			It("should restore the tasks", func() {
				// another empty spec, because gomock handles this
			})
		})
		Context("when some nodes are allocated", func() {
			BeforeEach(func() {
				initNodes = []*api.Node{
					{},
					{
						Attachments: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "nw1"}, Addresses: []string{"192.168.1.4/24"}},
							{Network: &api.Network{ID: "nw2"}, Addresses: []string{"192.168.2.4/24"}},
						},
					},
					{
						Attachments: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "nw3"}, Addresses: []string{"192.168.3.4/24"}},
							{Network: &api.Network{ID: "nw4"}, Addresses: []string{"192.168.4.4/24"}},
						},
					},
				}
				attachments := append(initNodes[1].Copy().Attachments, initNodes[2].Copy().Attachments...)
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, attachments).Return(nil)
				mockDriver.EXPECT().Restore(nil).Return(nil)
			})
			It("should not return an error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
			It("should restore all of the attachments", func() {
				// empty case, handled by gomock
			})
		})
		Context("when some tasks and some nodes are allocated", func() {
			BeforeEach(func() {
				initNodes = []*api.Node{
					{},
					{
						Attachments: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "nw1"}, Addresses: []string{"192.168.1.4/24"}},
							{Network: &api.Network{ID: "nw2"}, Addresses: []string{"192.168.2.4/24"}},
						},
					},
					{
						Attachments: []*api.NetworkAttachment{
							{Network: &api.Network{ID: "nw3"}, Addresses: []string{"192.168.3.4/24"}},
							{Network: &api.Network{ID: "nw4"}, Addresses: []string{"192.168.4.4/24"}},
						},
					},
				}
				initTasks = []*api.Task{
					// Empty task, should add any attachments
					{},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{}, Addresses: []string{"192.168.1.4/24"}},
							{Network: &api.Network{}, Addresses: []string{"192.168.2.4/24"}},
						},
					},
					{
						Networks: []*api.NetworkAttachment{
							{Network: &api.Network{}, Addresses: []string{"192.168.3.4/24"}},
							{Network: &api.Network{}, Addresses: []string{"192.168.4.4/24"}},
						},
					},
				}
				attachments := append(initTasks[1].Copy().Networks,
					append(initTasks[2].Copy().Networks,
						append(initNodes[1].Copy().Attachments,
							initNodes[2].Copy().Attachments...,
						)...,
					)...,
				)
				mockPort.EXPECT().Restore([]*api.Endpoint{})
				mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, attachments).Return(nil)
				mockDriver.EXPECT().Restore(nil).Return(nil)
			})
			It("should restore all of the attachments", func() {
				// handled by gomock
			})
			It("should return no error", func() {
				Expect(err).ToNot(HaveOccurred())
			})
		})
		Context("when errors occur", func() {
			BeforeEach(func() {
				// port can't return an error
				mockPort.EXPECT().Restore([]*api.Endpoint{})
			})
			Context("from the ipam allocator", func() {
				BeforeEach(func() {
					mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, []*api.NetworkAttachment{}).Return(errors.ErrBadState("foo"))
				})
				It("should return the error", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(WithTransform(errors.IsErrBadState, BeTrue()))
				})
			})
			Context("from the driver allocator", func() {
				BeforeEach(func() {
					mockIpam.EXPECT().Restore(nil, []*api.Endpoint{}, []*api.NetworkAttachment{}).Return(nil)
					mockDriver.EXPECT().Restore(nil).Return(errors.ErrInternal("bar"))
				})
				It("should return the error", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(WithTransform(errors.IsErrInternal, BeTrue()))
				})
			})
		})
	})
	// everything here gets its own describe block so that we can share the
	// common gomock setup
	Describe("Allocating and deallocating", func() {
		BeforeEach(func() {
			// Expectations for gomock to fulfill Restore. We pass an "Any"
			// matcher because we're not actually testing this behavior, we
			// just need to fill up the calls for gomock.
			mockPort.EXPECT().Restore(gomock.Any())
			mockIpam.EXPECT().Restore(gomock.Any(), gomock.Any(), gomock.Any()).Return(nil)
			mockDriver.EXPECT().Restore(gomock.Any()).Return(nil)
		})

		JustBeforeEach(func() {
			// just before, we should prepare for a bunch of calls to
			// IsNetworkNodeLocal
			for _, nw := range initNetworks {
				// use the driver name "local" to indicate node-local networks
				if nw.DriverState != nil && nw.DriverState.Name == "local" {
					mockDriver.EXPECT().IsNetworkNodeLocal(nw).Return(true, nil)
				} else {
					mockDriver.EXPECT().IsNetworkNodeLocal(nw).Return(false, nil)
				}
			}
			// Before we start, do a restore of all of these pre-populated
			// items.

			// NOTE(dperny): this doens't actually do a whole bunch for us,
			// because the only state persisted in this version of the
			// Allocator is that of allocated services, but this future-proofs
			// the test at basically no cost.
			a.Restore(initNetworks, initServices, initTasks, initNodes)
		})

		Describe("allocating networks", func() {
			var (
				net *api.Network
				err error
			)
			BeforeEach(func() {
				net = &api.Network{
					ID: "net1",
				}
			})
			JustBeforeEach(func() {
				err = a.AllocateNetwork(net)
			})
			Context("when the network is overlay", func() {
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(false, nil)
					mockIpam.EXPECT().AllocateNetwork(net).Return(nil)
					mockDriver.EXPECT().Allocate(net).Return(nil)
				})
				It("should return no error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
			})
			Context("when the network is node-local", func() {
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(true, nil)
					mockDriver.EXPECT().Allocate(net).Return(nil)
				})
				It("should not call the IPAM allocator", func() {
					// covered by mock
				})
				It("should return no error", func() {
					Expect(err).ToNot(HaveOccurred())
				})
			})
			Context("when the network driver is invalid", func() {
				rerr := errors.ErrInvalidSpec("invalid driver")
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(false, rerr)
				})
				It("should return the error returned by IsNetworkNodeLocal", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(Equal(rerr))
				})
				It("should not modify the object", func() {
					Expect(net).To(Equal(&api.Network{ID: "net1"}))
				})
			})
			Context("when the IPAM allocator returns an error", func() {
				rerr := errors.ErrInternal("foo")
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(false, nil)
					mockIpam.EXPECT().AllocateNetwork(net).Return(rerr)
				})
				It("should return the error returned by ipam.AllocateNetwork", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(Equal(rerr))
				})
				It("should not modify the object", func() {
					Expect(net).To(Equal(&api.Network{ID: "net1"}))
				})
			})
			Context("when the driver allocator returns an error", func() {
				rerr := errors.ErrInternal("foo")
				BeforeEach(func() {
					mockDriver.EXPECT().IsNetworkNodeLocal(net).Return(false, nil)
					mockIpam.EXPECT().AllocateNetwork(net).Return(nil)
					mockDriver.EXPECT().Allocate(net).Return(rerr)
					mockIpam.EXPECT().DeallocateNetwork(net)
				})
				It("should return the error returned by driver.Allocate", func() {
					Expect(err).To(HaveOccurred())
					Expect(err).To(Equal(rerr))
				})
				It("should roll back the IPAM allocations", func() {
					// this is another case here just for documentation, it is
					// covered by gomock
				})
				It("should not modify the object", func() {
					Expect(net).To(Equal(&api.Network{ID: "net1"}))
				})
			})
		})

		Describe("allocating services", func() {
			var (
				service *api.Service
				err     error
			)
			BeforeEach(func() {
				// add an ingress network
				ingress := &api.Network{
					ID: "ingress",
					Spec: api.NetworkSpec{
						Ingress: true,
					},
				}
				local := &api.Network{
					ID: "localnet",
					DriverState: &api.Driver{
						Name: "local",
					},
				}
				initNetworks = append(initNetworks, ingress, local)

				initService := &api.Service{
					ID: "service1",
					SpecVersion: &api.Version{
						Index: 1,
					},
					Spec: api.ServiceSpec{
						Endpoint: &api.EndpointSpec{
							Mode: api.ResolutionModeVirtualIP,
							Ports: []*api.PortConfig{
								{
									Name:          "foo",
									TargetPort:    80,
									PublishedPort: 8080,
									Protocol:      api.ProtocolTCP,
									PublishMode:   api.PublishModeIngress,
								},
							},
						},
						Task: api.TaskSpec{
							Networks: []*api.NetworkAttachmentConfig{
								&api.NetworkAttachmentConfig{
									Target: "nw1",
								},
							},
						},
					},
					Endpoint: &api.Endpoint{
						Spec: &api.EndpointSpec{
							Mode: api.ResolutionModeVirtualIP,
							Ports: []*api.PortConfig{
								{
									Name:          "foo",
									TargetPort:    80,
									PublishedPort: 8080,
									Protocol:      api.ProtocolTCP,
									PublishMode:   api.PublishModeIngress,
								},
							},
						},
						Ports: []*api.PortConfig{
							{
								Name:          "foo",
								TargetPort:    80,
								PublishedPort: 8080,
								Protocol:      api.ProtocolTCP,
								PublishMode:   api.PublishModeIngress,
							},
						},
						VirtualIPs: []*api.Endpoint_VirtualIP{
							&api.Endpoint_VirtualIP{
								Addr:      "192.168.3.3/24",
								NetworkID: "nw1",
							},
							&api.Endpoint_VirtualIP{
								Addr:      "192.168.4.3/24",
								NetworkID: "ingress",
							},
						},
					},
				}
				initServices = append(initServices, initService)

				service = initService.Copy()
			})
			JustBeforeEach(func() {
				err = a.AllocateService(service)
			})
			Context("when the exact same service is passed", func() {
				It("should return ErrAlreadyAllocated", func() {
					Expect(err).To(And(
						HaveOccurred(),
						WithTransform(errors.IsErrAlreadyAllocated, BeTrue()),
					))
				})
			})
			Context("when the service is already fully allocated", func() {
				BeforeEach(func() {
					service.SpecVersion.Index = 5
				})
				It("should return ErrAlreadyAllocated", func() {
					Expect(err).To(And(
						HaveOccurred(),
						WithTransform(errors.IsErrAlreadyAllocated, BeTrue()),
					))
				})
				It("should update the locally cached service", func() {
					Expect(a.services).To(HaveKey(service.ID))
					Expect(a.services[service.ID].SpecVersion.Index).To(Equal(uint64(5)))
				})
			})
			Context("when the service's tasks have node-local network attachments", func() {
				BeforeEach(func() {
					service.Spec.Task.Networks = append(
						service.Spec.Task.Networks,
						&api.NetworkAttachmentConfig{
							Target: "localnet",
						},
					)
				})
				It("should not allocate a VIP for the node-local network", func() {
					Expect(a.nodeLocalNetworks).To(HaveKey("localnet"))
					// covered by gomock
				})
			})
			PContext("when the port allocator returns an error", func() {
				BeforeEach(func() {

				})
			})
			PContext("when the IPAM allocator returns an error", func() {
			})
			PContext("when the IPAM allocator return ErrAlreadyAllocated", func() {
			})
			PContext("when the service exposes ports, meaning it attaches to ingress", func() {
			})
		})

		PDescribe("allocating tasks", func() {
			BeforeEach(func() {

			})
		})

		PDescribe("allocating nodes", func() {
		})
	})

	Describe("IsServiceFullyAllocated", func() {
		var (
			service *api.Service
			result  bool
		)
		BeforeEach(func() {
			// create a service pre-populated with all of the pointer values so we
			// can just do assignments in the tests
			service = &api.Service{
				Spec: api.ServiceSpec{
					Endpoint: &api.EndpointSpec{},
				},
				Endpoint: &api.Endpoint{
					Spec: &api.EndpointSpec{},
				},
			}
		})
		JustBeforeEach(func() {
			result = a.isServiceFullyAllocated(service)
		})
		Context("when the spec and endpoint are both nil", func() {
			BeforeEach(func() {
				service.Endpoint = nil
				service.Spec.Endpoint = nil
			})
			It("should return true", func() {
				Expect(result).To(BeTrue())
			})
		})
		Context("when the service's resolution mode does not match the spec's", func() {
			BeforeEach(func() {
				service.Endpoint.Spec.Mode = api.ResolutionModeDNSRoundRobin
				service.Spec.Endpoint.Mode = api.ResolutionModeVirtualIP
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})
		Context("when the endpoint VIPs and network attachments have different lengths", func() {
			BeforeEach(func() {
				service.Endpoint.VirtualIPs = []*api.Endpoint_VirtualIP{
					{
						NetworkID: "nw1",
						Addr:      "192.168.1.1/24",
					},
				}
				service.Spec.Task.Networks = []*api.NetworkAttachmentConfig{
					{
						Target: "nw1",
					},
					{
						Target: "nw2",
					},
				}
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})
		Context("when the endpoint has VIPs for network", func() {
			BeforeEach(func() {
				service.Endpoint.VirtualIPs = []*api.Endpoint_VirtualIP{
					{
						NetworkID: "nw1",
						Addr:      "192.168.1.1/24",
					},
					{
						NetworkID: "nw3",
						Addr:      "192.168.2.1/24",
					},
				}
				service.Spec.Task.Networks = []*api.NetworkAttachmentConfig{
					{
						Target: "nw1",
					},
					{
						Target: "nw2",
					},
				}
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})

		Context("when the ports do not match", func() {
			BeforeEach(func() {
				// we don't need to test the functionality of AlreadyAllocated,
				// just create a case where we know it will return false.
				service.Spec.Endpoint.Ports = []*api.PortConfig{
					{
						Name: "foo",
					},
				}
			})
			It("should return false", func() {
				Expect(result).To(BeFalse())
			})
		})
		Context("when the service is totally empty", func() {
			BeforeEach(func() {
				service = &api.Service{ID: "foo"}
			})
			It("should return true", func() {
				Expect(result).To(BeTrue())
			})
		})
	})
})
